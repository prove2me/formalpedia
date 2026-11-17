-- Prove2me | Theorems.Thm_LiuZhangBRW_Concentration_Supplement_theorem_C_1
-- name    : LiuZhangBRW.Concentration.Supplement.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:04:30.989856+00:00
-- url     : https://prove2.me/theorems/4e30d274-3f04-4569-973a-68b9be850042
-- title:
--   Theorem C.1 — subcritical Galton–Watson: $\mathbb E e^{\theta\xi}<\infty$ for some $\theta>0$ $\iff$ $\mathbb E e^{\delta Z}<\infty$ for some $\delta>0$
-- statement:
--   Let $(p_k)_{k \ge 0}$ be an offspring distribution on $\mathbb N$ with mean $m = \sum_k k\,p_k < 1$ (a **subcritical** law). On a probability space let $(\xi_{n,i})_{n,i \ge 0}$ be independent random variables with law $p$, where $\xi_{n,i}$ is the number of children of the $i$-th individual of generation $n$, and let the generation sizes be
--   $$
--   Z_0 = 1, \qquad Z_{n+1} = \sum_{i=0}^{Z_n - 1} \xi_{n,i}.
--   $$
--   Let $\xi = \xi_{0,0}$ be the number of offspring of the ancestor, and let $Z = \sum_{n \ge 0} Z_n \in \mathbb N \cup \{\infty\}$ be the total progeny. Then
--   $$
--   \mathbb E\big[e^{\theta \xi}\big] < \infty \text{ for some } \theta > 0
--   \iff
--   \mathbb E\big[e^{\delta Z}\big] < \infty \text{ for some } \delta > 0 .
--   $$
--
--   A subcritical Galton–Watson tree thus has an exponentially integrable total size exactly when its offspring law does. The paper uses this to control population sizes in branching random walks.
--
--   **Formalization Note** The process is written inline, in the encoding of the platform's `GaltonWatson.extinction_criterion` (offspring law a `PMF ℕ`, an independent array indexed by $\mathbb N \times \mathbb N$, the recursion for $Z_n$). The mean is computed in $[0,\infty]$. $Z$ is not assumed finite: $e^{\delta Z}$ is the supremum of $e^{\delta(Z_0 + \dots + Z_{N-1})}$ over $N$, which is $\infty$ where $Z = \infty$. Both expectations are lower Lebesgue integrals in $[0,\infty]$, so "$< \infty$" is literal finiteness.
--
--   Differences from the source:
--
--   - encoding: a subcritical Galton–Watson process; Z the total number of descendents → offspring law p : PMF ℕ with Σ k p_k < 1; independent ξ_{n,i} with law p; Z_0 = 1, Z_{n+1} = Σ_{i<Z_n} ξ_{n,i}; Z = Σ_{n≥0} Z_n (ancestor included), possibly infinite; reason: the standard construction, as in the proof (Z_0 = 1); counting the ancestor multiplies E e^{δZ} by e^δ only, so the finiteness claim is unchanged
--   - encoding: E[e^{δZ}] and E[e^{θξ}] < ∞ → lower Lebesgue integrals in [0, ∞], with e^{δZ} = sup_N e^{δ(Z_0 + ⋯ + Z_{N−1})}; reason: a Bochner integral would be 0 on a non-integrable function; the supremum equals e^{δZ} where Z < ∞ and ∞ where Z = ∞, so the expectation is the paper's
-- source:
--   Liu, Zhang, Concentration Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs, arXiv:1601.04794 (artifact sha256 7499631b9d550f66e791c0b3df0879f26102f111fee3052e363ebbff0c72bdcb; no version stamp), Appendix C, Theorem C.1, p. 49

import Mathlib

open MeasureTheory ProbabilityTheory

namespace LiuZhangBRW.Concentration

namespace Supplement

/-- Theorem C.1, exponential moments of a subcritical Galton–Watson process (Liu, Zhang,
*Concentration Inequalities for Branching Random Walks with Applications to Phase Transitions in
CSPs*, arXiv:1601.04794, artifact sha256 7499631b…bdcb, Appendix C, Theorem C.1, p. 49). Let `Z`
be the total number of descendants and `ξ` the number of offspring of the ancestor. For a
subcritical Galton–Watson process, `E[e^{θξ}] < ∞` for some `θ > 0` if and only if
`E[e^{δZ}] < ∞` for some `δ > 0`.

**Formalization Note** The process is written inline, in the encoding of the platform's
`GaltonWatson.extinction_criterion`: the offspring law is `p : PMF ℕ`; the offspring numbers
`ξ n i` (children of the `i`-th individual of generation `n`) are measurable, mutually independent
over `(n, i) ∈ ℕ × ℕ`, each with law `p`; the generation sizes satisfy `Z 0 = 1` and
`Z (n+1) = ∑_{i < Z n} ξ n i`. Subcritical means `m = ∑ k p_k < 1` (mean in `[0, ∞]`); nothing
else is assumed. The ancestor's offspring is `ξ 0 0` (= `Z 1`). The total progeny is
`Z = ∑_{n ≥ 0} Z_n` (ancestor included, as in the proof's `Z_0 = 1`; excluding it changes
`E e^{δZ}` by the factor `e^δ` only). It is not assumed finite: `e^{δZ}` is the increasing limit
`⨆_N e^{δ (Z_0 + ⋯ + Z_{N−1})}` in `[0, ∞]`, which is `∞` where `Z = ∞`. Both expectations are
lower Lebesgue integrals in `[0, ∞]`, so `< ∞` is literal finiteness (a Bochner integral would be
`0` on a non-integrable function). -/
theorem theorem_C_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : PMF ℕ) (hsub : ∑' k : ℕ, (k : ENNReal) * p k < 1)
    (ξ : ℕ → ℕ → Ω → ℕ) (hξ_meas : ∀ n i, Measurable (ξ n i))
    (hξ_indep : iIndepFun (fun ni : ℕ × ℕ => ξ ni.1 ni.2) P)
    (hξ_law : ∀ n i k, P (ξ n i ⁻¹' {k}) = p k)
    (Z : ℕ → Ω → ℕ) (hZ0 : ∀ ω, Z 0 ω = 1)
    (hZ : ∀ n ω, Z (n + 1) ω = ∑ i ∈ Finset.range (Z n ω), ξ n i ω) :
    (∃ θ : ℝ, 0 < θ ∧
        ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (ξ 0 0 ω : ℝ))) ∂P < ⊤) ↔
      (∃ δ : ℝ, 0 < δ ∧
        ∫⁻ ω, (⨆ N : ℕ, ENNReal.ofReal
          (Real.exp (δ * ∑ j ∈ Finset.range N, (Z j ω : ℝ)))) ∂P < ⊤) := by sorry

end Supplement

end LiuZhangBRW.Concentration
