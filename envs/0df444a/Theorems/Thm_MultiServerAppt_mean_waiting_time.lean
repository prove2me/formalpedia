-- Prove2me | Theorems.Thm_MultiServerAppt_mean_waiting_time
-- name    : MultiServerAppt.mean_waiting_time
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:12.364499+00:00
-- url     : https://prove2.me/theorems/de892d99-6545-402a-abdc-d6405bf36a02
-- title:
--   Eq. (17) — mean waiting times (corrected: $S^{(1)}=S$)
-- statement:
--   In the D/PH/s model, for $1\le i\le m$ the matrix $S_i^{\mathrm{wait}}$ is nonsingular, $W_{s+i}$ is integrable, and $\mathbb E W_{s+i}=-\alpha_i^{\mathrm{wait}}(S_i^{\mathrm{wait}})^{-1}\mathbf 1$. Hence
--
--   $$\sum_{i=s+1}^{n}\mathbb E W_i=\sum_{i=1}^{n-s}-\alpha_i^{\mathrm{wait}}\big(S_i^{\mathrm{wait}}\big)^{-1}\mathbf 1.$$
--
--   This is the waiting term of the objective.
--
--   Differences from the source:
--   - correction: printed start of the recursion S^(1) = 1 (p.12) → S^(1) = S, through Sblock; reason: the printed value is false: at s = 1, S = (-1), α = (1) it gives F_M(t) = 1 - e^t < 0
--   - generalization: the sum over clients, Eq. (17) → each mean separately, and the sum; reason: the sum follows from the separate means, which are what p.14 derives from F_W
--   - generalization: mean service time normalized to E B_i = 1 (p.9) → any PH(α, S) with S nonsingular; reason: the normalization is without loss of generality and the paper's case is an instance
--   - encoding: α holds initial probabilities; S^{-1} and finite means are used (pp.9, 10, 14) → ∑ α = 1 and IsUnit S.det are fields next to the published IsPHRep; reason: IsPHRep allows an atom at 0 and defective phases, which the source excludes; no instance of the source is lost
--   - encoding: states (j, m) and matrices ordered in blocks by j descending → a sum type of saturated and unsaturated states, indexed by i with N = s + i; reason: a Lean convention; block order does not matter to a function of states
--   - encoding: E W_i and (S_i^wait)^{-1} used without comment → IsUnit (det S_i^wait) and Integrable W_{s+i} stated as conclusions; reason: the page's expectations and inverses presuppose them; stating them rules out the junk values of the Bochner integral and Matrix.inv, and no instance of the source is lost
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (17), p.14

import Mathlib
import Definitions.Def_MultiServerAppt_IsDPHSModel
import Definitions.Def_MultiServerAppt_W
import Definitions.Def_MultiServerAppt_waitMat
import Definitions.Def_MultiServerAppt_waitAlpha

open Matrix MeasureTheory

namespace MultiServerAppt

/-- Eq. (17): `S_i^wait` is nonsingular, `W_{s+i}` is integrable with mean
`-α_i^wait (S_i^wait)⁻¹ 𝟙`, and the sum over clients is the sum of these means. Kuiper–Lee,
Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (17), p.14.

**Formalization Note** `Integrable` and `IsUnit` are conclusions: without them a Bochner integral and
`Matrix.inv` could hold junk values. -/
theorem mean_waiting_time {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {s m : ℕ} {α : ι → ℝ} {S : Matrix ι ι ℝ}
    {x : ℕ → ℝ} {B : ℕ → Ω → ℝ} (hM : IsDPHSModel P s m α S x B) :
    (∀ i ∈ Finset.Icc 1 m,
      IsUnit (waitMat α S s i).det ∧
      Integrable (fun ω => W s x (fun c => B c ω) (s + i)) P ∧
      ∫ ω, W s x (fun c => B c ω) (s + i) ∂P =
        -(waitAlpha α S s x i ⬝ᵥ ((waitMat α S s i)⁻¹ *ᵥ fun _ => (1 : ℝ)))) ∧
    ∑ c ∈ Finset.Icc (s + 1) (s + m), ∫ ω, W s x (fun c => B c ω) c ∂P =
      ∑ i ∈ Finset.Icc 1 m,
        -(waitAlpha α S s x i ⬝ᵥ ((waitMat α S s i)⁻¹ *ᵥ fun _ => (1 : ℝ))) := by sorry

end MultiServerAppt
