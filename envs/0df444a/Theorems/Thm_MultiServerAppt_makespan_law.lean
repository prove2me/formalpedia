-- Prove2me | Theorems.Thm_MultiServerAppt_makespan_law
-- name    : MultiServerAppt.makespan_law
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:01:42.743563+00:00
-- url     : https://prove2.me/theorems/f7a10e8e-3e10-4dfe-b3da-4f8ea7447f2d
-- title:
--   The makespan distribution and mean, pp.14-15 (corrected: $S^{(1)}=S$)
-- statement:
--   In the D/PH/s model, for $1\le i\le m$ and $t\ge 0$,
--
--   $$F_{M_{s+i}}(t)=p_0^{(s+i)}(t)=1-\alpha_{s+i}\exp(S_{s+i}t)\mathbf 1.$$
--
--   Moreover $S_{s+i}$ is nonsingular, $M_{s+i}$ is integrable, and $\mathbb E M_{s+i}=-\alpha_{s+i}S_{s+i}^{-1}\mathbf 1$.
--
--   At $i=n-s$ this is the session length, the input of the idle time and the overtime.
--
--   Differences from the source:
--   - correction: printed start of the recursion S^(1) = 1 (p.12) → S^(1) = S, through Sblock; reason: the printed value is false: at s = 1, S = (-1), α = (1) it gives F_M(t) = 1 - e^t < 0
--   - generalization: mean service time normalized to E B_i = 1 (p.9) → any PH(α, S) with S nonsingular; reason: the normalization is without loss of generality and the paper's case is an instance
--   - encoding: α holds initial probabilities; S^{-1} and finite means are used (pp.9, 10, 14) → ∑ α = 1 and IsUnit S.det are fields next to the published IsPHRep; reason: IsPHRep allows an atom at 0 and defective phases, which the source excludes; no instance of the source is lost
--   - encoding: states (j, m) and matrices ordered in blocks by j descending → a sum type of saturated and unsaturated states, indexed by i with N = s + i; reason: a Lean convention; block order does not matter to a function of states
--   - encoding: E M_{s+i} and S_{s+i}^{-1} used without comment → IsUnit (det S_{s+i}) and Integrable M_{s+i} stated as conclusions; reason: the page's expectations and inverses presuppose them; stating them rules out the junk values of the Bochner integral and Matrix.inv, and no instance of the source is lost
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.2, displays for $F_{M_{s+i}}$ and $\mathbb{E} M_{s+i}$, pp.14-15

import Mathlib
import Definitions.Def_MultiServerAppt_IsDPHSModel
import Definitions.Def_MultiServerAppt_M
import Definitions.Def_MultiServerAppt_alphaSys

open Matrix MeasureTheory

namespace MultiServerAppt

/-- The makespan distribution `F_{M_{s+i}}(t) = 1 - α_{s+i} exp(S_{s+i} t) 𝟙` and its mean
`E M_{s+i} = -α_{s+i} S_{s+i}⁻¹ 𝟙`, for `i = 1, …, n - s`. Kuiper–Lee, Appointment Scheduling for
Multiple Servers, SSRN 3975471, §4.2, displays for `F_{M_{s+i}}` and `E M_{s+i}`, pp.14-15. -/
theorem makespan_law {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {s m : ℕ} {α : ι → ℝ} {S : Matrix ι ι ℝ}
    {x : ℕ → ℝ} {B : ℕ → Ω → ℝ} (hM : IsDPHSModel P s m α S x B)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 m) :
    (∀ t : ℝ, 0 ≤ t →
      P.real {ω | M s x (fun c => B c ω) (s + i) ≤ t} =
        1 - (alphaSys α S s x i ᵥ* NormedSpace.exp (t • sysMat α S s i)) ⬝ᵥ fun _ => (1 : ℝ)) ∧
    IsUnit (sysMat α S s i).det ∧
    Integrable (fun ω => M s x (fun c => B c ω) (s + i)) P ∧
    ∫ ω, M s x (fun c => B c ω) (s + i) ∂P =
      -(alphaSys α S s x i ⬝ᵥ ((sysMat α S s i)⁻¹ *ᵥ fun _ => (1 : ℝ))) := by sorry

end MultiServerAppt
