-- Prove2me | Theorems.Thm_OnDemandCoord_eq_15
-- name    : OnDemandCoord.eq_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:37.116821+00:00
-- url     : https://prove2.me/theorems/70d6a0bb-2857-472a-aaf7-4ecebde6ea4c
-- title:
--   (15) (corrected: adds $c\sum_iQ^*_i$): the platform's profit $\Pi^*$, and participation under (16′) and (17)
-- statement:
--   **(15)–(17)** (pp. 21–22). Let $(Q^*,\eta^*)$ be a system optimum, $S^*=NG(\eta^*)$, $\beta^*$ an optimal solution of (8) with all $\beta^*_i>0$, $m_i$ from (14) and any fees $r_i$. For any run data and every $T\ge2$, under the TFRB policy $\kappa_T$:
--   1. the platform's expected profit is $$\Pi^*=p\sum_{i\in I}(1-m_i)\,\mathbb E[(X_i-Q^*_i)^+]-C(Q^*,\eta^*)+c\sum_{i\in I}Q^*_i+\sum_{i\in I}r_i ;$$
--   2. if the fees satisfy (16′), $\sum_ir_i\ge C(Q^*,\eta^*)-c\sum_iQ^*_i-p\sum_i(1-m_i)\mathbb E[(X_i-Q^*_i)^+]$, then $\Pi^*\ge0$;
--   3. for each firm $i$ whose fee satisfies (17), $r_i\le h^p_i-(p(1-m_i)\mathbb E[(X_i-Q^*_i)^+]+cQ^*_i)$, the firm's cost at $Q^*$ is at most its stand-alone cost $h^p_i$.
--
--   Differences from the source:
--   - encoding: the model of §3 (continuous nonnegative demands with finite mean, any joint law; G continuous, log-concave, with density g > 0 on [τ̲, τ̄]) → OnDemandCoord.Model: X_i measurable, integrable, ≥ 0 a.s., atomless law; G continuous, monotone, 0 left of τ̲, 1 right of τ̄, G′ = g > 0 within [τ̲, τ̄], log G concave on (τ̲, τ̄]; reason: readings of the standing assumptions, stated once on the definition; no instance of the paper is excluded
--   - correction: (15): Π* = pΣ(1 − m_i)E[(X_i − Q_i*)⁺] − C(Q*, η*) + Σ r_i, and (16) without −cΣQ_i* → Π* with the term + cΣQ_i*, and (16′) with − cΣQ_i*; reason: the display on p. 20 derives Π = −C + pΣ(1 − m_i)E[X̂_i] + cΣQ_i + Σr_i; n = 1, X ~ Exp(1), p = 2, c = 1, G uniform on [0.95, 1.95], N = 10 gives Π* = r − 0.2438, not r − 0.6869 (paper.md item 1)
--   - encoding: w_i^F and w_i^C divide by β*_i → β*_i > 0 for every i; reason: (11)–(12) are undefined at β*_i = 0
--   - generalization: h^p_i at the permanent-only level Q^p → h^p_i at any staffing vector in (17); reason: the implication holds for any reference vector; it specializes to Q^p
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), (15)–(17), pp. 21–22; display on p. 20

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory

/-- **(15) and participation, corrected**, Lu–Zheng–Zhong, SSRN:2783617 (PDF of 2023-05-13), pp. 21–22. Under the TFRB policy and the contract
with `m_i` from (14), the platform's profit is
`Π* = p ∑_i (1 − m_i) E[(X_i − Q_i*)⁺] − C(Q*, η*) + c ∑_i Q_i* + ∑_i r_i`. (16′) gives `Π* ≥ 0`, and
(17) for firm `i` gives `h_i(Q_i*) ≤ h_i^p`.

**Formalization Note.** Printed (15) lacks the term `c ∑_i Q_i*` of the display on p. 20. -/
theorem eq_15 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Qp Qstar : Fin n → ℝ) (ηstar : ℝ) (hopt : M.IsSystemOptimum Qstar ηstar)
    (K : Contract n) (hm : K.m = M.mParam Qstar)
    (hβ : M.IsOptimalLP Qstar (M.S ηstar) K.β) (hpos : ∀ i, 0 < K.β i)
    (run : RunData n (M.S ηstar)) (T : ℕ) (hT : 2 ≤ T) :
    M.platformProfit K ηstar (M.tfrb Qstar (M.S ηstar) K.β run T) Qstar =
        M.p * ∑ i, (1 - K.m i) * M.mean Qstar i - M.C Qstar ηstar +
          M.c * ∑ i, Qstar i + ∑ i, K.r i ∧
      (M.FeeLower Qstar ηstar K.m K.r →
        0 ≤ M.platformProfit K ηstar (M.tfrb Qstar (M.S ηstar) K.β run T) Qstar) ∧
      ∀ i, M.FeeUpper Qp Qstar K.m K.r i →
        M.firmCost K i Qstar (M.tfrb Qstar (M.S ηstar) K.β run T) ηstar ≤ M.hp Qp i := by sorry

end OnDemandCoord
