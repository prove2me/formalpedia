-- Prove2me | Theorems.Thm_MasulloRH_principal_cell_weighted_endpoint_derivative_jump
-- name    : MasulloRH.principal_cell_weighted_endpoint_derivative_jump
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T20:17:01.894871+00:00
-- url     : https://prove2.me/theorems/d1377673-b704-441b-b69b-f445ee5f8275
-- title:
--   One-sided cutoff derivatives of the floor-cell pole convolution recover the weighted prime sample
-- statement:
--   For any real compactly supported continuous test f, L>0, α>0, let r=exp(−αL). Use the actual causal pole profile, equal on cell m to −√(2α) r^(m+1) exp(α(x−mL)), and its full convolution V with s↦exp(−bs) f(s). The endpoint density is the finite weighted sum of the positive prime samples up to floor(x/L) minus the pointwise product of this pole profile and V. Its primitive from zero has one-sided derivatives at every positive boundary x₀=(n+1)L. The theorem identifies both derivatives with the corresponding cell extensions and proves that the right derivative minus r² times the left derivative equals (1−r²)exp(−x₀/2) f(x₀). It also proves continuity of the convolution and local integrability of the density. For the physical half twist take b=1/2−α and L=log p.
-- source:
--   Masullo mission, corrected bare-width endpoint extraction, shell_trace_endpoint_jump. This native real-analysis step proves the derivative jump including the pole convolution for every fixed test. Identification of the model with the recentered global Hilbert-space trace is the separate paper argument in the mission discussion. Related accepted calculations concern the finite atomic overlap and the normalized cell autocorrelation.

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Filter Set
open scoped Topology

theorem MasulloRH.principal_cell_weighted_endpoint_derivative_jump (L α b : ℝ) (hL : 0 < L) (hα : 0 < α)
    (f : ℝ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (n : ℕ) :
    let r := Real.exp (-α*L)
    let cell := fun (m : ℕ) (x : ℝ) => -Real.sqrt (2*α) *
      Real.exp (-α*x+α*(2*(x-L*(m:ℝ))-L))
    let g := fun x : ℝ => if 0 ≤ x then cell ⌊x/L⌋₊ x else 0
    let V := fun x : ℝ => ∫ t : ℝ, g t * (Real.exp (-b*(x-t))*f (x-t))
    let A := fun m : ℕ => (1-r^2) * ∑ k ∈ Finset.range m,
      (r^2)^(m-1-k) * (Real.exp (-((k:ℝ)+1)*L/2) * f (((k:ℝ)+1)*L))
    let d := fun x : ℝ => A ⌊x/L⌋₊ - g x * V x
    let x₀ := ((n:ℝ)+1)*L
    let dLeft := A n - cell n x₀ * V x₀
    let dRight := A (n+1) - cell (n+1) x₀ * V x₀
    Continuous V ∧ LocallyIntegrable d volume ∧
    Tendsto d (𝓝[<] x₀) (𝓝 dLeft) ∧ Tendsto d (𝓝[>] x₀) (𝓝 dRight) ∧
    HasDerivWithinAt (fun R => ∫ t in 0..R, d t) dLeft (Iic x₀) x₀ ∧
    HasDerivWithinAt (fun R => ∫ t in 0..R, d t) dRight (Ici x₀) x₀ ∧
    dRight - r^2*dLeft = (1-r^2)*Real.exp (-x₀/2)*f x₀ := by sorry
