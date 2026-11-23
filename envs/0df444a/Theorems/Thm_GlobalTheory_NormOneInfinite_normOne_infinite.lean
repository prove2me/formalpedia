-- Prove2me | Theorems.Thm_GlobalTheory_NormOneInfinite_normOne_infinite
-- name    : GlobalTheory.NormOneInfinite.normOne_infinite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:52.204814+00:00
-- url     : https://prove2.me/theorems/879173de-d160-4b21-ac42-ea12455008d0
-- title:
--   Norm One Infinite: norm One infinite
-- statement:
--   The Norm One Infinite construction uses the norm One infinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormOneInfinite.lean#L5-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/NormOneInfinite.lean#L5-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormOneInfinite

theorem GlobalTheory.NormOneInfinite.normOne_infinite {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E]
    (c : Gal(E/F)) (hc : ∀ x : E, (c : E → E) ((c : E → E) x) = x) (h1 : c ≠ (1 : Gal(E/F))) :
    Set.Infinite {l : E | l * (c : E → E) l = (1 : E)} := by sorry
