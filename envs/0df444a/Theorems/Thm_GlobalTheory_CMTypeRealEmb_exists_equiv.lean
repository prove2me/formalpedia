-- Prove2me | Theorems.Thm_GlobalTheory_CMTypeRealEmb_exists_equiv
-- name    : GlobalTheory.CMTypeRealEmb.exists_equiv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:04:22.737798+00:00
-- url     : https://prove2.me/theorems/a18306a2-1dde-4812-bd8b-5be2eba84def
-- title:
--   CMType Real Emb: exists equiv
-- statement:
--   The CMType Real Emb construction uses the exists equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEquivCmTypeRealEmbeddingsMaxRealSubfield.lean#L16-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEquivCmTypeRealEmbeddingsMaxRealSubfield.lean#L16-L69

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivCmTypeRealEmbeddingsMaxRealSubfield
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.CMTypeRealEmb

theorem GlobalTheory.CMTypeRealEmb.exists_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) :
    ∃ e : I ≃ Emb (maximalRealSubfield E), ∀ (i : I) (a : maximalRealSubfield E),
      φ i (a : E) = ((e i a : ℝ) : ℂ) := by sorry
