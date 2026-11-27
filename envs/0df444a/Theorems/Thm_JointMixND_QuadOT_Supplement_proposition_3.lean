-- Prove2me | Theorems.Thm_JointMixND_QuadOT_Supplement_proposition_3
-- name    : JointMixND.QuadOT.Supplement.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T03:11:24.042112+00:00
-- url     : https://prove2.me/theorems/b99ee734-fd67-4773-a963-b060d4a9b7bb
-- title:
--   Proposition 3, p. 7 — a tuple with finite variances that supports an NCD joint mix satisfies 2 max σ_i² ≤ Σ σ_i², condition (4)
-- statement:
--   Let $F_1,\dots,F_n$ be distributions on $\mathbb R$ with finite variances $\sigma_1^2,\dots,\sigma_n^2$. If $(F_1,\dots,F_n)$ supports an NCD joint mix, i.e. there is a random vector $\mathbf X$ with $X_i\sim F_i$, $\sum_iX_i$ almost surely constant and $\operatorname{Cov}(X_i,X_j)\le0$ for $i\ne j$, then
--
--   $$2\max_{i\in[n]}\sigma_i^2\le\sum_{i\in[n]}\sigma_i^2.\tag{4}$$
--
--   Condition (4) is therefore necessary for NCD joint mixes, and hence also for NOD and NA joint mixes, with arbitrary marginals of finite variance. It is the necessity half of Theorem 2.
--
--   **Formalization Note** Each $F_i$ is a probability measure with $\int x^2\,dF_i<\infty$; since the marginals are square integrable, Mathlib's covariance in the published `IsNCD` is the genuine covariance. Condition (4) is written as $2\sigma_j^2\le\sum_i\sigma_i^2$ for every $j$.
--
--   Differences from the source:
--   - encoding: a random vector X = (X_1, …, X_n) with components indexed by [n] → its law P on Fin n → ℝ, coordinates 0-based; reason: every notion involved depends on X only through its law; same instances
--   - encoding: 2 max_{i∈[n]} σ_i² ≤ Σ_{i∈[n]} σ_i² → ∀ j, 2 σ_j² ≤ Σ_i σ_i²; reason: equivalent for n ≥ 1; needs no special case at n = 0
--   - generalization: vectors of positive dimension n → n : ℕ, including n = 0; reason: at n = 0 there is no j and the conclusion is vacuous; all positive-dimensional source instances are retained
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, p. 7, Proposition 3, (4) (proof p. 23)

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Basic
import Definitions.Def_JointMixND_QuadOT_Supplement_Dependence

open MeasureTheory ProbabilityTheory

namespace JointMixND.QuadOT.Supplement

theorem proposition_3 {n : ℕ} (F : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (F i)]
    (hF : ∀ i, MemLp id 2 (F i))
    (hP : ∃ P : Measure (Fin n → ℝ), HasMarginals F P ∧ IsJointMix P ∧ IsNCD P) :
    ∀ j : Fin n, 2 * variance id (F j) ≤ ∑ i, variance id (F i) := by sorry

end JointMixND.QuadOT.Supplement
