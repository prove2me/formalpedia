-- Prove2me | Theorems.Thm_JointMixND_QuadOT_proposition_5
-- name    : JointMixND.QuadOT.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:54.364336+00:00
-- url     : https://prove2.me/theorems/15d62516-8138-4436-a4a1-c978ed94eab4
-- title:
--   Proposition 5, p. 11 — for symmetric 𝓜, an exchangeable NCD joint mix with correlation P*_n does at least as well as any joint mix
-- statement:
--   Let $F$ be a distribution on $\mathbb R$ with finite second moment, let $\mathcal M$ be a symmetric set of probabilities on $2^{[n]}$, and let $\mathbf X=(X_1,\dots,X_n)$ be a joint mix with identical marginals $F$. Then there exists an exchangeable NCD joint mix $\mathbf X^{\mathrm E}$ with marginals $F$ and correlation matrix $P^*_n$ such that
--   $$\sup_{\mu\in\mathcal M}C^f_\mu(\mathbf X^{\mathrm E})\le\sup_{\mu\in\mathcal M}C^f_\mu(\mathbf X)$$
--   for every measurable $f:\mathbb R\to\mathbb R$ for which the expectations $\mathbb E[f(\sum_{i\in K}X_i)]$, $K\subseteq[n]$, exist.
--
--   The same vector $\mathbf X^{\mathrm E}$ works for all such $f$ at once. Among all joint mixes with marginals $F$, the exchangeable NCD ones with correlation matrix $P^*_n$ are therefore the better choices under uncertainty about which components are aggregated, for every cost function simultaneously.
--
--   **Formalization Note** The vector $\mathbf X^{\mathrm E}$ is represented by its law. The paper says "for all measurable functions $f$"; the cost (7) needs the expectations to exist, so the inequality is asserted for measurable $f$ with $f(\sum_{i\in K}X_i)$ integrable under the law of $\mathbf X$ for every $K$ (a Bochner integral of a non-integrable function is $0$ in Lean). The conclusion also asserts that these expectations exist under the law of $\mathbf X^{\mathrm E}$, so the left-hand side is a genuine value rather than Lean's junk $0$. The finite second moment of $F$ is §4's standing assumption (p. 9); it makes the covariances in "correlation matrix $P^*_n$" well defined. The witness is existential and comes before the quantifier over $f$, as printed.
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, p. 11, Proposition 5

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Problems

namespace JointMixND.QuadOT

open MeasureTheory ProbabilityTheory

/-- Proposition 5, p. 11. For a symmetric uncertainty set `𝓜` and a joint mix `X` with identical
marginals `F` (finite second moment, §4's standing assumption), there is one exchangeable NCD joint
mix `X^E` with marginals `F` and correlation matrix `P*_n` whose worst-case cost `sup_{μ∈𝓜} C^f_μ`
is at most that of `X`, simultaneously for every measurable `f` for which the expectations
`E[f(∑_{i∈K} X_i)]` exist; those expectations then also exist for `X^E`, so its cost is a genuine
value and not the Bochner integral's junk `0`. -/
theorem proposition_5 {n : ℕ} (F : Measure ℝ) [IsProbabilityMeasure F] (hF2 : MemLp id 2 F)
    (M : Set (Finset (Fin n) → ℝ)) (hM : M ⊆ ProbOnSubsets n) (hsymm : IsSymmetric M)
    (P : Measure (Fin n → ℝ)) (hP : IsCoupling F P) (hJM : IsJointMix P) :
    ∃ PE : Measure (Fin n → ℝ), IsCoupling F PE ∧ IsExchangeable PE ∧ IsJointMix PE ∧
      IsNCD PE ∧ HasCorrPstar F PE ∧
      ∀ f : ℝ → ℝ, Measurable f →
        (∀ K : Finset (Fin n), Integrable (fun x => f (∑ i ∈ K, x i)) P) →
        (∀ K : Finset (Fin n), Integrable (fun x => f (∑ i ∈ K, x i)) PE) ∧
          worstCost f M PE ≤ worstCost f M P := by sorry

end JointMixND.QuadOT
