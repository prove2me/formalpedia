-- Prove2me | Theorems.Thm_LeGallBrownianMap_theorem_2_3
-- name    : LeGallBrownianMap.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:36.42828+00:00
-- url     : https://prove2.me/theorems/928c8bb4-81f3-486d-9ff7-14d95769b0bc
-- title:
--   Theorem 2.3 — subsequential limits $(e,Z,D)$ of contour, labels and distances, and GH convergence to $(m_\infty,D)$
-- statement:
--   Let $p\ge2$ and let $\theta_n$ be uniform on $\mathbb T^p_n$, with contour function $C^n$, label function $\Lambda^n$ and interpolated distance process $d_n$ in the BDG map; $m_n=\tau^\circ_n\cup\{\partial\}$. From every sequence of integers tending to $\infty$ one can extract a subsequence $(n_k)$ along which
--
--   $$
--   \big(\lambda_pn^{-1/2}C^n_{pnt},\ \kappa_pn^{-1/4}\Lambda^n_{pnt},\ \kappa_pn^{-1/4}d_n(pns,pnt)\big)_{0\le s,t\le1}\xrightarrow{(d)}(e_t,Z_t,D(s,t))_{0\le s,t\le1}, \tag{5}
--   $$
--
--   where $(e,Z)$ are a normalized excursion and Brownian labels, and $D$ is a continuous random pseudometric on $[0,1]$ such that
--
--   1. (a) $D(s,s_*)=Z_s+\Delta=D^\circ(s,s_*)$ for every $s$;
--   2. (b) $D(s,t)\le D^*(s,t)\le D^\circ(s,t)$ for all $s,t$;
--   3. almost surely, for all $s,t$: $D(s,t)=0$ iff $D^*(s,t)=0$, iff $D^\circ(p_e(s),p_e(t))=0$;
--   4. along the same subsequence, $(m_n,\kappa_pn^{-1/4}d_{gr})$ converges in distribution, in the Gromov–Hausdorff sense, to $(m_\infty,D)$, $m_\infty=[0,1]/\!\approx$ with $s\approx t$ iff $D(s,t)=0$.
--
--   This is the compactness step of the bipartite case: the rest of the paper proves $D=D^*$, which removes the subsequence.
--
--   **Formalization Note** The conclusion is existential in a probability space carrying $(e,Z,D)$ with $e=$ `OAI.FKCRT.standardExcursion B`. $D^\circ(p_e(s),p_e(t))=0$ is written as the existence of representatives $s'\sim_e s$, $t'\sim_e t$ with $D^\circ(s',t')=0$. The law of the rooted pointed map $M_n$ is expressed through $\theta_n$ (`uniformTreeExpectation`, `bdgGH`).
--
--   Differences from the source:
--   - encoding: from every sequence of integers converging to ∞ → from every strictly increasing φ : ℕ → ℕ, a strictly increasing ψ with convergence along φ ∘ ψ; reason: every sequence tending to ∞ has a strictly increasing subsequence, so the two forms are equivalent
--   - encoding: the pair (e, Z) as in Section 2.4 → ∃ three independent Brownian motions B on the same space with e = standardExcursion B, and IsBrownianLabels; reason: the Bessel-bridge realization of the normalized excursion and the conditional Gaussian law of the labels
--   - encoding: convergence in distribution of continuous processes → convergence of expectations of bounded functions continuous for the uniform topology on functions (UniformFun), with a.s. continuous limit paths; reason: the continuous functions form a closed subspace of the uniform function space; the notions agree
--   - encoding: M_n uniform on M^p_n with vertex set m_n and d_gr → θ_n uniform on T^p_n, with the BDG graph on τ°_n ∪ {∂}; reason: the paper's identification via the BDG bijection (p.15–16)
--   - reading: properties (a), (b) and the pseudometric property of the random process D → stated almost surely (one null set for all s, t); reason: statements about a random process; the paper's later use is almost sure
--   - encoding: (m∞, D) random compact metric spaces, GH convergence in distribution → a.e.-measurability of ω ↦ ([0,1]/{D = 0}, D) in K, and convergence of E f for every bounded continuous f : K → ℝ; reason: definition of convergence in distribution in K; makes the limit law well defined
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, Theorem 2.3, pp.16–17, eq. (5)

import Mathlib
import Definitions.Def_FKCRT
import Definitions.Def_LeGallBrownianMap_ghMeasurableSpace
import Definitions.Def_LeGallBrownianMap_IsBDGSubseqLimit
import Definitions.Def_LeGallBrownianMap_IsBrownianLabels
import Definitions.Def_LeGallBrownianMap_dCirc
import Definitions.Def_LeGallBrownianMap_dStar
import Definitions.Def_LeGallBrownianMap_sStar
import Definitions.Def_LeGallBrownianMap_labelDelta
import Definitions.Def_LeGallBrownianMap_pseudoQuotientGH
import Definitions.Def_LeGallBrownianMap_bdgGH
import Definitions.Def_LeGallBrownianMap_kappaP

open MeasureTheory ProbabilityTheory Filter GromovHausdorff OAI.FKCRT
open scoped Topology NNReal BoundedContinuousFunction

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, Theorem 2.3,
pp.16–17: "From every sequence of integers converging to ∞, we can extract a subsequence
(n_k)_{k≥1} along which the following convergence in distribution of continuous processes holds:
(λ_p n^{−1/2} C^n_{pnt}, κ_p n^{−1/4} Λ^n_{pnt}, κ_p n^{−1/4} d_n(pns, pnt)) −(d)→
(e_t, Z_t, D(s, t)), (5) where the pair (e, Z) is as in Section 2.4, and (D(s, t)) is a continuous
random process such that the function (s, t) ↦ D(s, t) defines a pseudometric on [0, 1]², and the
following properties hold: (a) D(s, s∗) = Z_s + ∆ = D°(s, s∗) for every s ∈ [0, 1]; (b)
D(s, t) ≤ D∗(s, t) ≤ D°(s, t) for every s, t ∈ [0, 1]. For every s, t ∈ [0, 1], we put s ≈ t if
D(s, t) = 0. Then, a.s. for every s, t ∈ [0, 1], the property s ≈ t holds if and only if
D∗(s, t) = 0 or, equivalently, D°(p_e(s), p_e(t)) = 0. Finally, set m∞ = [0, 1]/≈ and equip m∞
with the distance induced by D, which is still denoted by D. Then, along the same sequence where
the convergence (5) holds, the random compact metric spaces (m_n, κ_p n^{−1/4} d_gr) converge in
distribution to (m∞, D) in the sense of the Gromov–Hausdorff convergence."
Here `θ_n = (τ_n, ℓ^n)` is uniform on `T^p_n`, `C^n`, `Λ^n` its contour and label functions,
`d_n` the interpolated distances between corners in the BDG map, `m_n = τ°_n ∪ {∂}`.

For `p ≥ 2` and every strictly increasing `φ`, there are a strictly increasing `ψ`, a probability
space and processes `e, Z, D` such that:
1. (5) holds along `n = φ(ψ(k))` (`IsBDGSubseqLimit`);
2. `(e, Z)` is as in §2.4: `e` is the normalized excursion `standardExcursion B` for three
   independent Brownian motions `B`, and `Z` is Brownian labels given `e`;
3. almost surely, `D` is a pseudometric on `[0,1]`, (a) and (b) hold;
4. almost surely, for all `s, t`: `D(s,t) = 0 ⇔ D∗(s,t) = 0`, and `D∗(s,t) = 0 ⇔` there are
   `s' ∼_e s`, `t' ∼_e t` with `D°(s', t') = 0` (i.e. `D°(p_e(s), p_e(t)) = 0`);
5. `ω ↦ (m∞, D) = ([0,1]/{D = 0}, D)` is a random variable in K, and along `φ ∘ ψ` the laws of
   `(m_n, κ_p n^{−1/4} d_gr)` converge to its law: `E f(m_n, …) → E f(m∞, D)` for every bounded
   continuous `f : K → ℝ`.

**Formalization Note.** "From every sequence of integers converging to ∞" is read for strictly
increasing sequences `φ` (every sequence tending to `∞` has a strictly increasing subsequence).
"(e, Z) as in Section 2.4" is realized with `e = standardExcursion B` (the Bessel-bridge
realization of the normalized excursion, published `OAI.FKCRT.standardExcursion`) and
`IsBrownianLabels`. `D°(p_e(s), p_e(t))` is the minimum of `D°` over representatives; `u ∼_e v`
is `OAI.FKCRT.excursionDist e u v = 0`. In (a)–(b), `D°(s,t)` is the function on `[0,1]²`
(`dCirc`). The rooted pointed map `M_n` uniform on `M^p_n` is the BDG image of `θ_n` uniform on
`T^p_n` (p.15), so its laws are the averages over `T^p_n` (`uniformTreeExpectation`) and its
vertex set with graph distance is `bdgGH`. Properties (a), (b), the pseudometric property and the
characterization of `≈` are almost sure statements (one null set for all `s, t`). -/
theorem theorem_2_3 (p : ℕ) (hp : 2 ≤ p) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
    ∃ (e Z : Ω → unitInterval → ℝ) (D : Ω → unitInterval → unitInterval → ℝ),
      IsBDGSubseqLimit p (φ ∘ ψ) e Z D P ∧
      (∃ B : Fin 3 → ℝ≥0 → Ω → ℝ, (∀ i, IsBrownianReal (B i) P) ∧
        iIndepFun (fun i ω t => B i t ω) P ∧ ∀ ω, e ω = standardExcursion B ω) ∧
      IsBrownianLabels e (fun t ω => Z ω t) P ∧
      (∀ᵐ ω ∂P,
        ((∀ s, D ω s s = 0) ∧ (∀ s t, D ω s t = D ω t s) ∧
          (∀ s t u, D ω s u ≤ D ω s t + D ω t u)) ∧
        (∀ s, D ω s (sStar (Z ω)) = Z ω s + labelDelta (Z ω) ∧
          Z ω s + labelDelta (Z ω) = dCirc (Z ω) s (sStar (Z ω))) ∧
        (∀ s t, D ω s t ≤ dStar (e ω) (Z ω) s t ∧ dStar (e ω) (Z ω) s t ≤ dCirc (Z ω) s t)) ∧
      (∀ᵐ ω ∂P, ∀ s t,
        (D ω s t = 0 ↔ dStar (e ω) (Z ω) s t = 0) ∧
        (dStar (e ω) (Z ω) s t = 0 ↔
          ∃ s' t', excursionDist (e ω) s s' = 0 ∧ excursionDist (e ω) t t' = 0 ∧
            dCirc (Z ω) s' t' = 0)) ∧
      AEMeasurable (fun ω => pseudoQuotientGH unitInterval (D ω)) P ∧
      ∀ f : GHSpace →ᵇ ℝ,
        Tendsto (fun k => uniformTreeExpectation p (φ (ψ k))
            (fun θ => f (bdgGH (kappaP p * ((φ (ψ k) : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) θ)))
          atTop (𝓝 (∫ ω, f (pseudoQuotientGH unitInterval (D ω)) ∂P)) := by sorry

end LeGallBrownianMap
