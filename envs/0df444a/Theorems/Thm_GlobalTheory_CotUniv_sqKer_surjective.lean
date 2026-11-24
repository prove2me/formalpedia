-- Prove2me | Theorems.Thm_GlobalTheory_CotUniv_sqKer_surjective
-- name    : GlobalTheory.CotUniv.sqKer_surjective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:27:17.49395+00:00
-- url     : https://prove2.me/theorems/689c88e4-e782-4d9d-b3bb-6da27a272de7
-- title:
--   Cot Univ: sq Ker surjective
-- statement:
--   The Cot Univ construction uses the sq Ker surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L134-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L134-L136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_UniversalDerivation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory GlobalTheory.CotUniv
variable {R₀ : Type} [CommRing R₀] (O : LAlg R₀)
  (M : Type) [AddCommGroup M] [Module (O : Type) M]
variable {O M}
variable (O M)
variable {O M}

theorem GlobalTheory.CotUniv.sqKer_surjective : Function.Surjective (sqKer : M → (sqProj O M).ker) := by sorry
