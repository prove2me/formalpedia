-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_vt_mul_io_shift
-- name    : GlobalTheory.Ex.NumD.vt_mul_io_shift
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:06:26.423956+00:00
-- url     : https://prove2.me/theorems/a68e7eb8-9f54-4543-b08a-11951e4ab2b6
-- title:
--   Num D: vt mul io shift
-- statement:
--   The Num D construction uses the vt mul io shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaConstantTermRepresentativeDependence.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaConstantTermRepresentativeDependence.lean#L12-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)

theorem GlobalTheory.Ex.NumD.vt_mul_io_shift (g : N.Gt) (w χ : N.X) :
    ((N.ψ w * g.s w : Oˣ) : O) * N.vt (g * N.io w) χ = N.vt g (χ + w) := by sorry
