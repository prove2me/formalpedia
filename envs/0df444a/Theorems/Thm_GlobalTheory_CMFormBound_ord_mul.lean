-- Prove2me | Theorems.Thm_GlobalTheory_CMFormBound_ord_mul
-- name    : GlobalTheory.CMFormBound.ord_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:34.265566+00:00
-- url     : https://prove2.me/theorems/cedae217-266c-4413-a8ba-aba21750a727
-- title:
--   CMForm Bound: ord mul
-- statement:
--   The CMForm Bound construction uses the ord mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodGaloisIntegral.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodGaloisIntegral.lean#L16-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CMFormBound
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]

theorem GlobalTheory.CMFormBound.ord_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : ord_vw O (x * y) = ord_vw O x + ord_vw O y := by sorry
