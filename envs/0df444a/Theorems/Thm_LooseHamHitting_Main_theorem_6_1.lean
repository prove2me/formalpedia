-- Prove2me | Theorems.Thm_LooseHamHitting_Main_theorem_6_1
-- name    : LooseHamHitting.Main.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:19:34.141303+00:00
-- url     : https://prove2.me/theorems/90d74f6a-236a-426e-bac7-362f9e378c63
-- title:
--   Theorem 6.1 — entropy stability for mixed Hamilton cycles: most directed edge marginals are close to n/(12m)
-- statement:
--   Let $G$ be a 3-graph on $n$ vertices with $m$ edges, $m/n\to\infty$, and $M$ a matching of $s\ge1$ pairs on the same vertex set, with a root pair and direction fixed. Let $C$ be a random $(G,M)$-respecting mixed Hamilton cycle with an arbitrary law, given its root orientation, and $\pi(w;u\to v)$ its directed edge marginals. Fix a constant $C$ and nonnegative $\xi,\delta\to0$, and suppose
--
--   (i) $|M|=o(n)$, $\Delta_1(G)\le3Cm/n$, $\Delta_2(G)=o(m/n)$;
--
--   (ii) for every $A$ with $V(M)\subseteq A\subseteq V(G)$ and $|A|=(n+s)/2$, $\big||G[A,\bar A]|-3m/8\big|\le3\delta m$;
--
--   (iii) $H[C]\ge\frac{n-s}2\log\frac{6m}n-(n-s)-\xi n$.
--
--   Then
--   $$\sum_{(w;u\to v)\in\vec G-V(M)}\Big|\pi(w;u\to v)-\frac n{12m}\Big|=O_C\Big(n\sqrt{\xi+\delta+\frac sn+\frac1{\log(3m/(n\Delta_2(G)))}}\Big).$$
--
--   Formally: for every $C$ there are $K>0$, $\eta>0$ and $N$ such that the bound holds with constant $K$ whenever $n\ge N$, $m/n\ge1/\eta$, $s\le\eta n$, $\Delta_2(G)\le\eta m/n$, $0\le\xi,\delta\le\eta$ and (i)–(iii) hold.
--
--   Differences from the source:
--   - encoding: m/n → ∞, |M| = o(n), Δ₂(G) = o(m/n), ξ, δ → 0, conclusion O_C(·) → ∀ C, ∃ K > 0, ∃ η > 0, ∃ N: n ≥ N, m/n ≥ 1/η, s ≤ η n, Δ₂ ≤ η m/n, 0 ≤ ξ, δ ≤ η imply the bound with K; reason: equivalent to the statement over sequences of instances with K depending only on C
--   - encoding: a random cycle C with an arbitrary distribution, in its root orientation → a law μ on the finite set of (G, M)-respecting cycles; π sums μ over cycles traversing {u, v, w} from u to v in the root orientation; reason: definition of the law and of π
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, pp. 20–21, Theorem 6.1

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph
import Definitions.Def_LooseHamHitting_Main_Entropy
import Definitions.Def_LooseHamHitting_Main_Marginals

set_option autoImplicit false

open Classical

namespace LooseHamHitting.Main

/-- Theorem 6.1: entropy stability for random mixed Hamilton cycles. The asymptotic hypotheses
(`m/n → ∞`, `|M| = o(n)`, `Δ₂(G) = o(m/n)`, `ξ, δ → 0`, `n → ∞`) are encoded uniformly through
`η` and `N`; the constant `K` of `O_C(·)` depends only on `C`. -/
theorem theorem_6_1 :
    ∀ C : ℝ, ∃ K : ℝ, 0 < K ∧ ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ,
      ∀ (β : Type*) (V : Finset β) (G M : Finset (Finset β)) (r₁ r₂ : β)
        (μ : Finset (Finset β) → ℝ) (ξ δ : ℝ) (n m s : ℕ),
        V.card = n → G.card = m → M.card = s →
        IsThreeGraph V G → IsMatching V M → 1 ≤ s → {r₁, r₂} ∈ M →
        IsLawOn (mixedHamCycles V G M) μ →
        N ≤ n → 1 / η ≤ (m : ℝ) / n → 0 ≤ ξ → ξ ≤ η → 0 ≤ δ → δ ≤ η →
        (s : ℝ) ≤ η * n →
        (maxDegree V G : ℝ) ≤ 3 * C * m / n →
        (maxCodegree V G : ℝ) ≤ η * ((m : ℝ) / n) →
        (∀ A : Finset β, matchedVerts M ⊆ A → A ⊆ V → 2 * (A.card : ℝ) = n + s →
          |((crossEdges G A (V \ A)).card : ℝ) - 3 * (m : ℝ) / 8| ≤ 3 * δ * m) →
        ((n : ℝ) - s) / 2 * Real.log (6 * (m : ℝ) / n) - ((n : ℝ) - s) - ξ * n ≤
          entropyOn (mixedHamCycles V G M) μ →
        ∑ t ∈ orientedTriplesOff V G M,
            |dirMarginal V G M μ r₁ r₂ t.1 t.2.1 t.2.2 - (n : ℝ) / (12 * m)| ≤
          K * ((n : ℝ) * Real.sqrt (ξ + δ + (s : ℝ) / n +
            1 / Real.log (3 * (m : ℝ) / (n * maxCodegree V G)))) := by sorry

end LooseHamHitting.Main
