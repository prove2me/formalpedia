-- Prove2me | Theorems.Thm_GlobalTheory_EigenPair_adj_baseChange
-- name    : GlobalTheory.EigenPair.adj_baseChange
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:56:57.920953+00:00
-- url     : https://prove2.me/theorems/f0efea7d-f8fd-4368-bd3b-a9801a89feab
-- title:
--   Eigen Pair: adj base Change
-- statement:
--   The Eigen Pair construction uses the adj base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralFifth.lean#L40-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralFifth.lean#L40-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralFifth
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
open GlobalTheory GlobalTheory.EigenPair
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.EigenPair.adj_baseChange {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {H : Type} [AddCommGroup H]
    [Module O H] (B : LinearMap.BilinForm O H) (f g : Module.End O H) (hfg : ∀ h h', B (f h) h' = B h (g h'))
    (x y : K ⊗[O] H) : B.baseChange K (f.baseChange K x) y = B.baseChange K x (g.baseChange K y) := by sorry
