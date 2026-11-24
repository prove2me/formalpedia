-- Prove2me | Theorems.Thm_GlobalTheory_ProductLeftMaps_main
-- name    : GlobalTheory.ProductLeftMaps.main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:04.95287+00:00
-- url     : https://prove2.me/theorems/c3b59eb5-f69e-4365-8147-242649613b84
-- title:
--   Product Left Maps: main
-- statement:
--   The Product Left Maps construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ProdLeftEqMaps.lean#L23-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ProdLeftEqMaps.lean#L23-L34

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

theorem GlobalTheory.ProductLeftMaps.main : ∀ {F A B E : Type} [inst : Field F] [inst_1 : CommRing A] [inst_2 : CommRing B]
    [inst_3 : CommRing E] [inst_4 : Algebra F A] [inst_5 : Algebra F B] [inst_6 : Algebra F E]
    (z : TensorProduct F (A × B) E),
    (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) :
        TensorProduct F (A × B) E → TensorProduct F A E) z = (0 : TensorProduct F A E) →
    (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) :
        TensorProduct F (A × B) E → TensorProduct F B E) z = (0 : TensorProduct F B E) →
    z = (0 : TensorProduct F (A × B) E) := by sorry
