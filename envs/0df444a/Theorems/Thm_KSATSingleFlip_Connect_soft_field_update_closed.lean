-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_update_closed
-- name    : KSATSingleFlip.Connect.soft_field_update_closed
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:55:48.790412+00:00
-- url     : https://prove2.me/theorems/ca8cb6b9-77f4-4a37-8299-1e76a88c7a12
-- title:
--   Soft-field update preserves symmetric finite-unfrozen-mass measures
-- statement:
--   For β ≥ 0, a symmetric soft-field measure with finite unfrozen mass is mapped to another symmetric finite measure with finite unfrozen mass, and both identities m(Rβν)=βe^{h(ν)} and u(Rβν)=βe^{u(ν)} hold. This combines the well-definedness and mass statements printed in Definition 4.2.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2 and equation (4.3), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_field_update_closed (ν : Measure ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hsym : Measure.map (fun z : ℝ => -z) ν = ν)
    (hu : (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν) ≠ ∞) :
    IsFiniteMeasure (Rbeta β ν) ∧
    Measure.map (fun z : ℝ => -z) (Rbeta β ν) = Rbeta β ν ∧
    (massM (Rbeta β ν)).toReal = β*Real.exp (hPot ν) ∧
    (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂(Rbeta β ν)) =
      ENNReal.ofReal (β*Real.exp ((∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν).toReal)) := by sorry
