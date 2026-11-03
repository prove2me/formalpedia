-- Prove2me | Theorems.Thm_OnDemandCoord_claim_1
-- name    : OnDemandCoord.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:12.470406+00:00
-- url     : https://prove2.me/theorems/3f15a3ac-a25f-41fb-9261-a4317902325d
-- title:
--   Claim 1: $\hat C(Q,S)$ is jointly convex
-- statement:
--   **Claim 1** (p. A1). Let $\hat C(Q,S)=p\,\mathbb E\big[(\sum_{i\in I}(X_i-Q_i)^+-S)^+\big]+G^{-1}(S/N)\,S+c\sum_{i\in I}Q_i$, where $G^{-1}$ is the inverse of $G$ on its support $[\underline\tau,\bar\tau]$. Then $\hat C$ is jointly convex in $(Q,S)$ on
--   $$\{(Q,S):\ Q\ge0,\ 0\le S\le N\}.$$
--
--   This is the change of variable $S=NG(\eta)$ that turns the system problem (5), which is not convex in $\eta$, into a convex one; it makes the first-order conditions of Theorem 1 sufficient.
--
--   Differences from the source:
--   - encoding: the model of §3 (continuous nonnegative demands with finite mean, any joint law; G continuous, log-concave, with density g > 0 on [τ̲, τ̄]) → OnDemandCoord.Model: X_i measurable, integrable, ≥ 0 a.s., atomless law; G continuous, monotone, 0 left of τ̲, 1 right of τ̄, G′ = g > 0 within [τ̲, τ̄], log G concave on (τ̲, τ̄]; reason: readings of the standing assumptions, stated once on the definition; no instance of the paper is excluded
--   - encoding: G⁻¹ (unqualified) → the inverse of G on [τ̲, τ̄] (Function.invFunOn); reason: G is strictly increasing there and S/N ∈ [0, 1]; same values
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), Claim 1, p. A1 (PDF 33)

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory

/-- **Claim 1**, Lu–Zheng–Zhong, SSRN:2783617 (PDF of 2023-05-13), p. A1 (PDF 33). `Ĉ(Q, S)` is jointly convex in `Q` and `S`
on `Q ≥ 0`, `0 ≤ S ≤ N`.

**Formalization Note.** `G⁻¹` is the inverse of `G` on `[τl, τu]`. -/
theorem claim_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n) :
    ConvexOn ℝ {z : (Fin n → ℝ) × ℝ | 0 ≤ z.1 ∧ z.2 ∈ Set.Icc 0 M.N}
      (fun z => M.Chat z.1 z.2) := by sorry

end OnDemandCoord
