-- Prove2me | Theorems.Thm_GlobalTheory_AdicQuot_map_val_mk_eq_iff
-- name    : GlobalTheory.AdicQuot.map_val_mk_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:46.836647+00:00
-- url     : https://prove2.me/theorems/9ad294d2-ed3e-4af1-92d4-7e87cfce1e41
-- title:
--   Adic Quot: map val mk eq iff
-- statement:
--   The Adic Quot construction uses the map val mk eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdicCompletionQuotientRingEquiv.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdicCompletionQuotientRingEquiv.lean#L46-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.AdicQuot
open AdicCompletion
variable {A : Type} [CommRing A] (J q : Ideal A)

theorem GlobalTheory.AdicQuot.map_val_mk_eq_iff (s : AdicCauchySequence J A) (n : ℕ) (c : A ⧸ q) :
    (map J (Submodule.mkQ q) (AdicCompletion.mk J A s)).val n = Submodule.Quotient.mk c ↔
      lev J q n (AdicCompletion.mk J A s) = Ideal.Quotient.mk _ c := by sorry
