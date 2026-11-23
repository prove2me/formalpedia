-- Prove2me | Theorems.Thm_GlobalTheory_SS_Dil_dd_mul
-- name    : GlobalTheory.SS.Dil.dd_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:53.457049+00:00
-- url     : https://prove2.me/theorems/508e6fc7-4700-488b-a67c-38e8643e77e5
-- title:
--   Dil: dd mul
-- statement:
--   The Dil construction uses the dd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/UnramifiedIdealLocusCharacterization.lean#L59-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Dil
variable {R B S : Type} [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S]

theorem GlobalTheory.SS.Dil.dd_mul (x y : B) :
    dd R B S (x * y) = algebraMap B S x • dd R B S y + algebraMap B S y • dd R B S x := by sorry
