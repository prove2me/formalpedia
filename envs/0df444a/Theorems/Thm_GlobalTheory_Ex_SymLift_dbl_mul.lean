-- Prove2me | Theorems.Thm_GlobalTheory_Ex_SymLift_dbl_mul
-- name    : GlobalTheory.Ex.SymLift.dbl_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:33:31.966171+00:00
-- url     : https://prove2.me/theorems/beb57f2c-8424-4691-9d09-468360ed35ee
-- title:
--   Sym Lift: dbl mul
-- statement:
--   The Sym Lift construction uses the dbl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormalisingFactor.lean#L71-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/NormalisingFactor.lean#L71-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactor
import Theorems.Thm_GlobalTheory_Ex_NumB_dbl_mul

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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.SymLift
variable {O : Type} [CommRing O] (N : NumD O)

theorem GlobalTheory.Ex.SymLift.dbl_mul (x y : N.A) :
    dbl N.θ N.σ (x * y) * (N.θ (x * y) x y * N.θ x x y * N.θ y x y) = dbl N.θ N.σ x * dbl N.θ N.σ y := by sorry
