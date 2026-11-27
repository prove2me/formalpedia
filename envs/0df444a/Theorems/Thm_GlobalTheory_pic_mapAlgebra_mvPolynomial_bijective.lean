-- Prove2me | Theorems.Thm_GlobalTheory_pic_mapAlgebra_mvPolynomial_bijective
-- name    : GlobalTheory.pic_mapAlgebra_mvPolynomial_bijective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:36.407853+00:00
-- url     : https://prove2.me/theorems/758c9255-96b0-5b67-bd67-ec5cf725a28e
-- title:
--   Global Theory: pic map Algebra mv Polynomial bijective
-- statement:
--   The Global Theory construction uses the pic map Algebra mv Polynomial bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UniqueFactorizationMonoidAddMonoidAlgebraOfFree.lean#L260-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UniqueFactorizationMonoidAddMonoidAlgebraOfFree.lean#L260-L264

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct AlgebraMonoidAlgebra
open AddMonoidAlgebra CommRing
open GlobalTheory
variable (A X : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]

theorem GlobalTheory.pic_mapAlgebra_mvPolynomial_bijective (σ : Type*) :
    Function.Bijective (Pic.mapAlgebra A (MvPolynomial σ A)) := by sorry
