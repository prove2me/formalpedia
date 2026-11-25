-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_fixedAlgEquiv_tmul
-- name    : GlobalTheory.GaloisDescent.fixedAlgEquiv_tmul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:15.547185+00:00
-- url     : https://prove2.me/theorems/9b3f8c9c-3566-4694-a75a-46e9ca287e3b
-- title:
--   Galois Descent: fixed Alg Equiv tmul
-- statement:
--   The Galois Descent construction uses the fixed Alg Equiv tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueHomogeneousIdealFixedSubalgebra.lean#L218-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueHomogeneousIdealFixedSubalgebra.lean#L218-L220

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueHomogeneousIdealFixedSubalgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L G A : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]
  [Ring A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]
  [MulSemiringAction G A] [SMulDistribClass G L A] [SMulCommClass G K A]

theorem GlobalTheory.GaloisDescent.fixedAlgEquiv_tmul [Finite G] [IsGaloisGroup G K L] (l : L)
    (a : FixedPoints.subalgebra K A G) : fixedAlgEquiv K L G A (l ⊗ₜ a) = l • (a : A) := by sorry
