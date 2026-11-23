-- Prove2me | Theorems.Thm_GlobalTheory_CotUniv_lieLift_mk
-- name    : GlobalTheory.CotUniv.lieLift_mk
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:14.786055+00:00
-- url     : https://prove2.me/theorems/ed4d48b9-8418-41dc-bc12-6fc37a4da6ca
-- title:
--   Cot Univ: lie Lift mk
-- statement:
--   The Cot Univ construction uses the lie Lift mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L187-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L187-L189

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
variable {O : Type} [CommRing O] {p g : ℕ} {M : Type} [AddCommGroup M] [Module O M]

theorem GlobalTheory.CotUniv.lieLift_mk (m : Fin g → M) (hm : ∀ k, p • m k = 0) (l : Fin g → O) :
    lieLift O m hm (Submodule.Quotient.mk l) = ∑ k, l k • m k := by sorry
