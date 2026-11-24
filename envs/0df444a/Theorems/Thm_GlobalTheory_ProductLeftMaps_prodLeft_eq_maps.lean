-- Prove2me | Theorems.Thm_GlobalTheory_ProductLeftMaps_prodLeft_eq_maps
-- name    : GlobalTheory.ProductLeftMaps.prodLeft_eq_maps
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:55:45.960735+00:00
-- url     : https://prove2.me/theorems/14bbdf71-809f-40f4-be89-40c91ca8a462
-- title:
--   Product Left Maps: prod Left eq maps
-- statement:
--   The Product Left Maps construction uses the prod Left eq maps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ProdLeftEqMaps.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ProdLeftEqMaps.lean#L7-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ProdLeftEqMaps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ProductLeftMaps
open TensorProduct

theorem GlobalTheory.ProductLeftMaps.prodLeft_eq_maps {F A B E : Type} [Field F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (z : TensorProduct F (A × B) E) :
    TensorProduct.prodLeft F F A B E z =
      ((Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) :
          TensorProduct F (A × B) E → TensorProduct F A E) z,
       (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) :
          TensorProduct F (A × B) E → TensorProduct F B E) z) := by sorry
