-- Prove2me | Theorems.Thm_OnDemandCoord_system_optimum_interior
-- name    : OnDemandCoord.system_optimum_interior
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:13.034938+00:00
-- url     : https://prove2.me/theorems/733cfcb6-2c4a-4a71-8631-e10cafd69c17
-- title:
--   Under the standing assumption $\underline\tau<\varphi^p$: $S^*>0$, $p\bar F_i(Q^*_i)\ge c$, $0\le m_i<1$ and $\mathbb E[(X_i-Q^*_i)^+]>0$
-- statement:
--   **The standing assumption of §5** (p. 14): $\underline\tau<\varphi^p$, which excludes part (i) of Theorem 1. Let $Q^p$ satisfy $p\bar F_i(Q^p_i)=c$ for all $i$ and assume $\underline\tau<\varphi^p$. Then every system optimum $(Q^*,\eta^*)$ satisfies:
--   1. $S^*=NG(\eta^*)>0$: the on-demand workforce is used;
--   2. for every firm $i$: $p\bar F_i(Q^*_i)\ge c$, so the parameter (14), $m_i=(p\bar F_i(Q^*_i)-c)/(p\bar F_i(Q^*_i))$, is well defined with $0\le m_i<1$;
--   3. for every firm $i$: $\mathbb E[(X_i-Q^*_i)^+]>0$.
--
--   These are the facts about the optimum that §5 uses: the contract (14) and the target fill rates of (8) need them. No hypothesis on the joint law of the demands is used.
--
--   Differences from the source:
--   - encoding: the model of §3 (continuous nonnegative demands with finite mean, any joint law; G continuous, log-concave, with density g > 0 on [τ̲, τ̄]) → OnDemandCoord.Model: X_i measurable, integrable, ≥ 0 a.s., atomless law; G continuous, monotone, 0 left of τ̲, 1 right of τ̄, G′ = g > 0 within [τ̲, τ̄], log G concave on (τ̲, τ̄]; reason: readings of the standing assumptions, stated once on the definition; no instance of the paper is excluded
--   - reading: 'we will henceforth assume τ < ϕp' (an assumption, with no stated consequence) → the consequences used in §5: S* > 0, pF̄_i(Q_i*) ≥ c, 0 ≤ m_i < 1, E[(X_i − Q_i*)⁺] > 0 at every system optimum; reason: the sentence is the hypothesis; the conclusions are what §5 needs from it (m_i of (14) and the LP (8) divide by these quantities)
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), §5, p. 14 (standing assumption); (14), p. 21

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory

/-- **Consequences of the standing assumption of §5**, Lu–Zheng–Zhong, SSRN:2783617 (PDF of 2023-05-13), p. 14. Under `τl < φ^p`, every
system optimum has `S* > 0`, and for every firm `p F̄_i(Q_i*) ≥ c` (so `m_i` of (14) is well defined,
with `0 ≤ m_i < 1`) and `E[(X_i − Q_i*)⁺] > 0`. No hypothesis on the joint law is used. -/
theorem system_optimum_interior {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Qp : Fin n → ℝ) (hQp : M.IsPermanentBenchmark Qp) (hφ : M.τl < M.phiP Qp)
    (Qstar : Fin n → ℝ) (ηstar : ℝ) (hopt : M.IsSystemOptimum Qstar ηstar) :
    0 < M.S ηstar ∧
      ∀ i, M.c ≤ M.p * M.Fbar i (Qstar i) ∧ 0 ≤ M.mParam Qstar i ∧ M.mParam Qstar i < 1 ∧
        0 < M.mean Qstar i := by sorry

end OnDemandCoord
