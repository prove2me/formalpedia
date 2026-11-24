-- Prove2me | Theorems.Thm_GlobalTheory_CotUniv_lieLift_basis
-- name    : GlobalTheory.CotUniv.lieLift_basis
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:26:47.922815+00:00
-- url     : https://prove2.me/theorems/7a959482-5b92-4679-934a-8a1a53981ee2
-- title:
--   Cot Univ: lie Lift basis
-- statement:
--   The Cot Univ construction uses the lie Lift basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L191-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L191-L196

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

theorem GlobalTheory.CotUniv.lieLift_basis (m : Fin g → M) (hm : ∀ k, p • m k = 0) (k : Fin g) :
    lieLift O m hm (lieBasis O p g k) = m k := by sorry
