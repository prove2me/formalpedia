-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_TraceDualDifferent_covol_eq_covolume
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol_eq_covolume
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:15:43.396658+00:00
-- url     : https://prove2.me/theorems/51c4db81-eb1e-4e1c-91a5-5e9a74239547
-- title:
--   Trace Dual Different: covol eq covolume
-- statement:
--   The Trace Dual Different construction uses the covol eq covolume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TraceDualDifferent.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/TraceDualDifferent.lean#L66-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
variable {F : Type} [Field F] [NumberField F]
open NumberField nonZeroDivisors
variable {F : Type} [Field F] [NumberField F]
open Classical

theorem GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol_eq_covolume [IsTotallyReal F]
    (M : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol (M : FractionalIdeal (𝓞 F)⁰ F) =
      ZLattice.covolume (mixedEmbedding.idealLattice F M) := by sorry
