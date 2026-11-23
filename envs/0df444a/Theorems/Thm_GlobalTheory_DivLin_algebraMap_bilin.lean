-- Prove2me | Theorems.Thm_GlobalTheory_DivLin_algebraMap_bilin
-- name    : GlobalTheory.DivLin.algebraMap_bilin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:00:32.830118+00:00
-- url     : https://prove2.me/theorems/6a0d818f-858b-43f1-86ec-42d918ccef9b
-- title:
--   Div Lin: algebra Map bilin
-- statement:
--   The Div Lin construction uses the algebra Map bilin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ScaledRestrictionEndomorphisms.lean#L24-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphisms
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
open GlobalTheory GlobalTheory.DivLin
variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
  {H : Type} [AddCommGroup H] [Module O H]

theorem GlobalTheory.DivLin.algebraMap_bilin (B : LinearMap.BilinForm O H) (x y : H) :
    algebraMap O K (B x y) = B.baseChange K (inK K H x) (inK K H y) := by sorry
