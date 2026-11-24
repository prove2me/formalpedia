-- Prove2me | Theorems.Thm_GlobalTheory_trdeg_le_of_ringEquiv_square
-- name    : GlobalTheory.trdeg_le_of_ringEquiv_square
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:03.865178+00:00
-- url     : https://prove2.me/theorems/9e89d6c8-00fd-429d-bfc1-54b7b5c684e7
-- title:
--   Global Theory: trdeg le of ring Equiv square
-- statement:
--   The Global Theory construction uses the trdeg le of ring Equiv square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ResidueFieldIsoInvCompSpec.lean#L6-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ResidueFieldIsoInvCompSpec.lean#L6-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsoInvCompSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory

theorem GlobalTheory.trdeg_le_of_ringEquiv_square {K L K' L' : Type} [Field K] [Field L] [Field K'] [Field L']
    (f : K →+* L) (f' : K' →+* L') (eK : K ≃+* K') (eL : L ≃+* L')
    (h : f'.comp (eK : K →+* K') = (eL : L →+* L').comp f) :
    @Algebra.trdeg K L _ _ f.toAlgebra ≤ @Algebra.trdeg K' L' _ _ f'.toAlgebra := by sorry
