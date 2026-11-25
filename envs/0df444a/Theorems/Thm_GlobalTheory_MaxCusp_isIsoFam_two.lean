-- Prove2me | Theorems.Thm_GlobalTheory_MaxCusp_isIsoFam_two
-- name    : GlobalTheory.MaxCusp.isIsoFam_two
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:29.601225+00:00
-- url     : https://prove2.me/theorems/f694310e-2e22-4633-955d-29b3f0a0204e
-- title:
--   Max Cusp: is Iso Fam two
-- statement:
--   The Max Cusp construction uses the is Iso Fam two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHermOfMemLZ.lean#L68-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHermOfMemLZ.lean#L68-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MaxCusp
open NumberField Complex MeasureTheory Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ}
variable (X : Data E r)

theorem GlobalTheory.MaxCusp.isIsoFam_two (G : Matrix (Fin r) (Fin r) E) (u : Fin 2 → Fin r → E) :
    IsIsoFam G u ↔ IsIsoPair G u := by sorry
