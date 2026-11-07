-- Prove2me | Theorems.Thm_LowTempGlauber_lemma_10
-- name    : LowTempGlauber.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:28:03.963522+00:00
-- url     : https://prove2.me/theorems/50c7de76-9c03-41c6-95f0-f37d544fbd55
-- title:
--   Lemma 10 (with Definition 9) — congestion of component switches: $\sum_{(I,J)\in\mathcal P_{Y\to Y^\prime}}\mu^+(I)\mu^+(J)\le 8n\lambda(d\ell\lambda)^k\mu^+(Y)P^+(Y,Y^\prime)$
-- statement:
--   Let $d\ge3$ and $\lambda>1$, let $G=(V^+\sqcup V^-,E)$ be a $d$-regular bipartite graph with $|V^\pm|=n$ and vertex activities $0<\lambda_v\le\lambda$, let $\mu$ be the hard-core law, $\mu^+=\mu(\cdot\mid\mathcal I^+)$, and let $P^+$ be single-site Glauber dynamics on $\mathcal I^+_G$ with proposals outside $\mathcal I^+_G$ rejected. Let $\ell,r\ge1$ be integers. Fix a vertex labelling and, for each connected vertex set $C$, an ordering of $C$ satisfying the cut bound of Lemma 8; these define the component switches $\gamma_{I,J,C}$ of Definition 9.
--
--   Consider a Glauber transition $Y\to Y'$ with $Y\ne Y'$, and let $\mathcal P_{Y\to Y'}$ be the set of pairs $(I,J)\in(\mathcal I^+\times\mathcal I^+)\setminus B_{\ell,r}$ with $M(I),M(J)\ge2\ell$ for which $Y\to Y'$ is traversed in the switch $\gamma_{I,J,C}$ of some component $C$ of $G[I\oplus J]$. With $k=d+d\lceil\log_2\ell\rceil+r$,
--   $$\sum_{(I,J)\in\mathcal P_{Y\to Y'}}\mu^+(I)\,\mu^+(J)\le8n\lambda\,(d\ell\lambda)^k\,\mu^+(Y)\,P^+(Y,Y').$$
--
--   This congestion bound turns the one-component reduction (6) into the weak Poincaré inequality of Lemma 7.
--
--   **Formalization Note** $P^+$ is heat-bath Glauber dynamics for $\mu^+$, which is the same chain as heat-bath Glauber dynamics for $\mu$ with moves leaving $\mathcal I^+$ rejected. A Glauber transition is a pair $Y\ne Y'$ in $\mathcal I^+$ with $P^+(Y,Y')>0$.
--
--   Differences from the source:
--   - generalization: the sweep order "given by Lemma 8" (one ordering per component) → any family of orderings ord C satisfying Lemma 8’s cut bound d⌈log₂|C|⌉ + exc(C) for every connected C; reason: the ordering constructed in Lemma 8 is such a family, and the proof uses only the cut bound
--   - encoding: "fix an arbitrary vertex labelling" → a universally quantified bijection lab : Vertex n ≃ Fin (n + n); reason: the statement holds for every labelling, as the page says
--   - encoding: the switch written as I₀ → I₁ → ⋯ → I_ℓ → the list of all configurations visited by the sweep; reason: the sweep may make more than ℓ moves (A-neighbour deletions); the list records exactly the moves Definition 9 describes
--   - reading: "a Glauber transition e = (Y → Y′) with Y ≠ Y′" → Y, Y′ ∈ I⁺, Y ≠ Y′ and P⁺(Y, Y′) > 0; reason: a transition of the chain P⁺ on I⁺; every move of a switch in P_{Y→Y′} is such a transition
--   - encoding: P⁺, Glauber dynamics on I⁺ with proposals outside I⁺ rejected → glauber μ⁺ (heat-bath dynamics of μ⁺); reason: the same transition matrix on I⁺
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Definition 9 and Lemma 10, p.10 (proof pp.12–13)

import Mathlib
import Definitions.Def_mm_mcmc
import Definitions.Def_LowTempGlauber_Disagreement

open Classical

namespace LowTempGlauber

open ExpanderBIS.RandomHardCore MarkovMixing

/-- Galanis–Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission (manuscript sha256 c41a38ff…), Lemma 10 with Definition 9, p.10 (proof pp.12–13).

Setting of Lemma 7: `d ≥ 3`, `λ > 1`, `G` a `d`-regular bipartite graph on `V⁺ ⊔ V⁻`, `|V±| = n`,
activities `0 < λ_v ≤ λ`, `μ` the hard-core law, `μ⁺ = μ(· | I⁺)`, `P⁺` single-site Glauber dynamics on
`I⁺` with proposals outside `I⁺` rejected; integers `ℓ, r ≥ 1`. Fix a vertex labelling and, for each
connected vertex set `C`, an ordering of `C` with the cut bound of Lemma 8. Consider a Glauber
transition `Y → Y'` with `Y ≠ Y'`. Let `P_{Y→Y'}` be the set of pairs
`(I, J) ∈ (I⁺ × I⁺) ∖ B_{ℓ,r}` with `M(I), M(J) ≥ 2ℓ` for which `Y → Y'` is traversed in the component
switch `γ_{I,J,C}` of some component `C` of `G[I ⊕ J]`. With `k = d + d⌈log₂ ℓ⌉ + r`,
`Σ_{(I,J) ∈ P_{Y→Y'}} μ⁺(I) μ⁺(J) ≤ 8 n λ (d ℓ λ)^k μ⁺(Y) P⁺(Y, Y')` (5).

**Formalization Note.** `P⁺` is `glauber μ⁺` (heat-bath Glauber for `μ⁺`, which never moves outside
`I⁺`, the same chain as heat-bath Glauber for `μ` with moves leaving `I⁺` rejected). A Glauber
transition is a pair `Y ≠ Y'` of states of `I⁺` with `P⁺(Y, Y') > 0`. The labelling `lab` and the
orderings `ord C` are arbitrary, subject to `IsCutOrder` (the conclusion of Lemma 8) for every
connected `C`; the page uses one Lemma-8 ordering per component. -/
theorem lemma_10 (n d : ℕ) (hd : 3 ≤ d) (G : SimpleGraph (Vertex n)) (hG : IsBipReg G d)
    (lam : ℝ) (hlam : 1 < lam) (act : Vertex n → ℝ) (hact : ∀ v, 0 < act v ∧ act v ≤ lam)
    (ℓ r : ℕ) (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r)
    (lab : Vertex n ≃ Fin (n + n)) (ord : Finset (Vertex n) → List (Vertex n))
    (hord : ∀ C : Finset (Vertex n), (G.induce (C : Set (Vertex n))).Connected →
      IsCutOrder G d C (ord C))
    (Y Y' : Vertex n → Bool) (hY : IPlus G Y) (hY' : IPlus G Y') (hne : Y ≠ Y')
    (hmove : 0 < glauber (condLaw (hcLaw G act) (IPlus G)) Y Y') :
    ∑ I, ∑ J,
        (if IPlus G I ∧ IPlus G J ∧ ¬ BadComp G ℓ r I J ∧
            2 * (ℓ : ℤ) ≤ mag I ∧ 2 * (ℓ : ℤ) ≤ mag J ∧
            ∃ C ∈ components G (disagree I J), Traverses Y Y' (switchPath G lab C I J (ord C))
          then condLaw (hcLaw G act) (IPlus G) I * condLaw (hcLaw G act) (IPlus G) J else 0) ≤
      8 * n * lam * ((d : ℝ) * ℓ * lam) ^ (d + d * Nat.clog 2 ℓ + r) *
        condLaw (hcLaw G act) (IPlus G) Y *
        glauber (condLaw (hcLaw G act) (IPlus G)) Y Y' := by sorry

end LowTempGlauber
