-- Prove2me | Theorems.Thm_GlobalTheory_OrbitCoord_det_fderiv_ne_zero_orbit
-- name    : GlobalTheory.OrbitCoord.det_fderiv_ne_zero_orbit
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:15:55.058882+00:00
-- url     : https://prove2.me/theorems/2175c9e7-46fe-50e8-b1ff-44ecfb06fe84
-- title:
--   Orbit Coord: det fderiv ne zero orbit
-- statement:
--   The Orbit Coord construction uses the det fderiv ne zero orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DetFderivNeZeroOrbit.lean#L51-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DetFderivNeZeroOrbit.lean#L51-L111

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetFderivNeZeroOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.OrbitCoord
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.OrbitCoord.det_fderiv_ne_zero_orbit : (KapGGStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ), X.IsSec L w0 → (∀ k, X.IsSec L (s k)) → ∀ x ∈ X.dom, w0 x ≠ 0 → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x) z) / w0 (cpt X (x) z) : V (nd X))) 0).det ≠ 0 → ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (lact γ (rmul x b)) z) / w0 (cpt X (lact γ (rmul x b)) z) : V (nd X))) 0).det ≠ 0) := by sorry
