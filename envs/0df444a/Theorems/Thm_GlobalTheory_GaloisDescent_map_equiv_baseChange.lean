-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_map_equiv_baseChange
-- name    : GlobalTheory.GaloisDescent.map_equiv_baseChange
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:06.765095+00:00
-- url     : https://prove2.me/theorems/ec093d05-797f-5e16-8778-25afa3490241
-- title:
--   Galois Descent: map equiv base Change
-- statement:
--   The Galois Descent construction uses the map equiv base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueHomogeneousIdealFixedSubalgebra.lean#L158-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueHomogeneousIdealFixedSubalgebra.lean#L158-L162

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
variable {K L G V : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]
  [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V]
  [DistribMulAction G V] [SMulDistribClass G L V]
variable [SMulCommClass G K V]
omit [MulSemiringAction G L] [SMulDistribClass G L V] [DistribMulAction G V]
  [SMulCommClass G K V]

theorem GlobalTheory.GaloisDescent.map_equiv_baseChange {N : Type*} [AddCommGroup N] [Module K N] {f : N →ₗ[K] V}
    (hf : IsBaseChange L f) (P : Submodule K N) :
    (P.baseChange L).map hf.equiv.toLinearMap = Submodule.span L (f '' P) := by sorry
