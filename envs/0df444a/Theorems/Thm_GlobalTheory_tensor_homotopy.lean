-- Prove2me | Theorems.Thm_GlobalTheory_tensor_homotopy
-- name    : GlobalTheory.tensor_homotopy
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:52:50.526213+00:00
-- url     : https://prove2.me/theorems/d3678cab-46c8-5fcd-bd2b-854bacbcf0f3
-- title:
--   Global Theory: tensor homotopy
-- statement:
--   The Global Theory construction uses the tensor homotopy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L313-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L313-L333

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
variable {K : Type u} [CommRing K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module K V']

theorem GlobalTheory.tensor_homotopy {D e h ε : Module.End K V} {D' e' h' : Module.End K V'}
    (hh : 1 - e = D * h + h * D) (hDe : D * e = 0) (heD : e * D = 0) (hDε : D * ε = -(ε * D))
    (hεe : ε * e = e * ε) (hεh : ε * h = -(h * ε)) (hεε : ε * ε = 1)
    (hh' : 1 - e' = D' * h' + h' * D') :
    (1 : Module.End K (V ⊗[K] V')) - TensorProduct.map e e' =
      (TensorProduct.map D 1 + TensorProduct.map ε D') *
          (TensorProduct.map h 1 + TensorProduct.map (ε * e) h') +
        (TensorProduct.map h 1 + TensorProduct.map (ε * e) h') *
          (TensorProduct.map D 1 + TensorProduct.map ε D') := by sorry
