-- Prove2me | Theorems.Thm_MultiServerAppt_mean_idle_time
-- name    : MultiServerAppt.mean_idle_time
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:01:52.23757+00:00
-- url     : https://prove2.me/theorems/01ec1035-5585-495b-8c24-a623618830ad
-- title:
--   Eq. (18) — mean idle time
-- statement:
--   In the D/PH/s model with $n=s+m$, the idle time $I^{(s)}$ is integrable and
--
--   $$\mathbb E I^{(s)}=s\,(\mathbb E M_n+t_n)-\sum_{i=1}^{n}\mathbb E B_i.$$
--
--   The total capacity of the session minus the time spent in service is the time servers spend idle.
--
--   **Formalization Note** $I^{(s)}$ is the integral of idle servers over the session, not the right side, so the equation has content.
--
--   Differences from the source:
--   - generalization: mean service time normalized to E B_i = 1 (p.9) → any PH(α, S) with S nonsingular; reason: the normalization is without loss of generality and the paper's case is an instance
--   - encoding: α holds initial probabilities; S^{-1} and finite means are used (pp.9, 10, 14) → ∑ α = 1 and IsUnit S.det are fields next to the published IsPHRep; reason: IsPHRep allows an atom at 0 and defective phases, which the source excludes; no instance of the source is lost
--   - encoding: E I^(s) used without comment → Integrable I^(s) stated as a conclusion; reason: the page's expectations and inverses presuppose them; stating them rules out the junk values of the Bochner integral and Matrix.inv, and no instance of the source is lost
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (18), p.15

import Mathlib
import Definitions.Def_MultiServerAppt_IsDPHSModel
import Definitions.Def_MultiServerAppt_idle

open MeasureTheory

namespace MultiServerAppt

/-- Eq. (18): `E I^(s) = s (E M_n + t_n) - ∑_{i=1}^n E B_i`. Kuiper–Lee, Appointment Scheduling for
Multiple Servers, SSRN 3975471, Eq. (18), p.15.

**Formalization Note** `I^(s)` is `idle`, the integral of idle servers over the session, not the right
side, so the equation has content; `n = s + m`. -/
theorem mean_idle_time {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {s m : ℕ} {α : ι → ℝ} {S : Matrix ι ι ℝ}
    {x : ℕ → ℝ} {B : ℕ → Ω → ℝ} (hM : IsDPHSModel P s m α S x B) :
    Integrable (fun ω => idle s x (fun c => B c ω) (s + m)) P ∧
    ∫ ω, idle s x (fun c => B c ω) (s + m) ∂P =
      (s : ℝ) * (∫ ω, M s x (fun c => B c ω) (s + m) ∂P + arr s x (s + m)) -
        ∑ c ∈ Finset.Icc 1 (s + m), ∫ ω, B c ω ∂P := by sorry

end MultiServerAppt
