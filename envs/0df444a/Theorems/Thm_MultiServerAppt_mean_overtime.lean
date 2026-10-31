-- Prove2me | Theorems.Thm_MultiServerAppt_mean_overtime
-- name    : MultiServerAppt.mean_overtime
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:01:59.698331+00:00
-- url     : https://prove2.me/theorems/87d0a921-d300-442f-9023-c885dc1ba88d
-- title:
--   Eq. (19) — mean overtime (corrected: $S^{(1)}=S$)
-- statement:
--   In the D/PH/s model with $n=s+m$ and any target $T$, the overtime $O^{(s)}$ is integrable and
--
--   $$\mathbb E O^{(s)}=s\int_0^\infty\max\{t+t_n-T,0\}\,\mathrm dF_{M_n}(t),$$
--
--   where $F_{M_n}$ has density $f(t)=\alpha_n\exp(S_nt)(-S_n\mathbf 1)$.
--
--   Differences from the source:
--   - correction: printed start of the recursion S^(1) = 1 (p.12) → S^(1) = S, through Sblock; reason: the printed value is false: at s = 1, S = (-1), α = (1) it gives F_M(t) = 1 - e^t < 0
--   - encoding: Stieltjes integral dF_{M_n}(t) → Lebesgue integral on (0, ∞) against the density α_n exp(S_n t) t_n; reason: F_{M_n} is continuous with F_{M_n}(0) = 0, so the two integrals agree
--   - generalization: T is the mean service total over s (p.15) → every real T; reason: Eq. (19) itself keeps T free; the paper's T is an instance
--   - generalization: mean service time normalized to E B_i = 1 (p.9) → any PH(α, S) with S nonsingular; reason: the normalization is without loss of generality and the paper's case is an instance
--   - encoding: α holds initial probabilities; S^{-1} and finite means are used (pp.9, 10, 14) → ∑ α = 1 and IsUnit S.det are fields next to the published IsPHRep; reason: IsPHRep allows an atom at 0 and defective phases, which the source excludes; no instance of the source is lost
--   - encoding: states (j, m) and matrices ordered in blocks by j descending → a sum type of saturated and unsaturated states, indexed by i with N = s + i; reason: a Lean convention; block order does not matter to a function of states
--   - encoding: E O^(s) used without comment → Integrable O^(s) stated as a conclusion; reason: the page's expectations and inverses presuppose them; stating them rules out the junk values of the Bochner integral and Matrix.inv, and no instance of the source is lost
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (19), p.15

import Mathlib
import Definitions.Def_MultiServerAppt_IsDPHSModel
import Definitions.Def_MultiServerAppt_overtime
import Definitions.Def_MultiServerAppt_alphaSys

open Matrix MeasureTheory

namespace MultiServerAppt

/-- Eq. (19): `E O^(s) = s ∫₀^∞ max{t + t_n - T, 0} dF_{M_n}(t)`, for every target `T`. Kuiper–Lee,
Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (19), p.15.

**Formalization Note** `F_{M_n}` is continuous with `F_{M_n}(0) = 0`, so the Stieltjes integral is
written with the density `f t = α_n exp(S_n t) t_n`, where `t_n = -S_n 𝟙`; `n = s + m`. -/
theorem mean_overtime {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {s m : ℕ} {α : ι → ℝ} {S : Matrix ι ι ℝ}
    {x : ℕ → ℝ} {B : ℕ → Ω → ℝ} (hM : IsDPHSModel P s m α S x B) (T : ℝ) :
    Integrable (fun ω => overtime s x (fun c => B c ω) (s + m) T) P ∧
    ∫ ω, overtime s x (fun c => B c ω) (s + m) T ∂P =
      (s : ℝ) * ∫ t in Set.Ioi (0 : ℝ),
        max (t + arr s x (s + m) - T) 0 *
          (alphaSys α S s x m ᵥ* NormedSpace.exp (t • sysMat α S s m)) ⬝ᵥ
            MatrixAnalytic.PH.exitRates (sysMat α S s m) := by sorry

end MultiServerAppt
