-- Prove2me | Theorems.Thm_GlobalTheory_SW_isUnit_det_im_of_mem_siegel
-- name    : GlobalTheory.SW.isUnit_det_im_of_mem_siegel
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:58.30084+00:00
-- url     : https://prove2.me/theorems/7fc45e48-8ab5-47fe-a295-8395c8c9b5c5
-- title:
--   SW: is Unit det im of mem siegel
-- statement:
--   The SW construction uses the is Unit det im of mem siegel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/CanonicalThetaExponentSymplecticInvariant.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/CanonicalThetaExponentSymplecticInvariant.lean#L9-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CanonicalThetaExponentSymplecticInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW

theorem GlobalTheory.SW.isUnit_det_im_of_mem_siegel {ι : Type} [Fintype ι] [DecidableEq ι] {τ : Matrix ι ι ℂ}
    (hτ : τ ∈ Siegel ι) : IsUnit (τ.map fun z => (z.im : ℂ)).det := by sorry
