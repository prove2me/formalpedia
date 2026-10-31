-- Prove2me | Theorems.Thm_MultiServerAppt_waiting_time_cdf
-- name    : MultiServerAppt.waiting_time_cdf
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:00.788237+00:00
-- url     : https://prove2.me/theorems/be43258f-fb83-4fd1-a28b-93899fe376df
-- title:
--   The waiting-time distribution, p.14 (corrected: $S^{(1)}=S$)
-- statement:
--   In the D/PH/s model, for $1\le i\le m$ and $t\ge 0$,
--
--   $$F_{W_{s+i}}(t)=\mathbb P(W_{s+i}\le t)=1-\alpha_i^{\mathrm{wait}}\exp\big(S_i^{\mathrm{wait}}t\big)\mathbf 1.$$
--
--   So the waiting time of each client has a phase-type law, possibly with an atom at $0$.
--
--   Differences from the source:
--   - correction: printed start of the recursion S^(1) = 1 (p.12) → S^(1) = S, through Sblock; reason: the printed value is false: at s = 1, S = (-1), α = (1) it gives F_M(t) = 1 - e^t < 0
--   - generalization: mean service time normalized to E B_i = 1 (p.9) → any PH(α, S) with S nonsingular; reason: the normalization is without loss of generality and the paper's case is an instance
--   - encoding: α holds initial probabilities; S^{-1} and finite means are used (pp.9, 10, 14) → ∑ α = 1 and IsUnit S.det are fields next to the published IsPHRep; reason: IsPHRep allows an atom at 0 and defective phases, which the source excludes; no instance of the source is lost
--   - encoding: states (j, m) and matrices ordered in blocks by j descending → a sum type of saturated and unsaturated states, indexed by i with N = s + i; reason: a Lean convention; block order does not matter to a function of states
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.2, display for $F_{W_{s+i}}$, p.14

import Mathlib
import Definitions.Def_MultiServerAppt_IsDPHSModel
import Definitions.Def_MultiServerAppt_W
import Definitions.Def_MultiServerAppt_waitMat
import Definitions.Def_MultiServerAppt_waitAlpha

open Matrix MeasureTheory

namespace MultiServerAppt

/-- The waiting-time distribution `F_{W_{s+i}}(t) = 1 - α_i^wait exp(S_i^wait t) 𝟙`, for
`i = 1, …, n - s`. Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.2,
display for `F_{W_{s+i}}`, p.14. -/
theorem waiting_time_cdf {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {s m : ℕ} {α : ι → ℝ} {S : Matrix ι ι ℝ}
    {x : ℕ → ℝ} {B : ℕ → Ω → ℝ} (hM : IsDPHSModel P s m α S x B)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 m) (t : ℝ) (ht : 0 ≤ t) :
    P.real {ω | W s x (fun c => B c ω) (s + i) ≤ t} =
      1 - (waitAlpha α S s x i ᵥ* NormedSpace.exp (t • waitMat α S s i)) ⬝ᵥ
        fun _ => (1 : ℝ) := by sorry

end MultiServerAppt
