-- Prove2me | Theorems.Thm_GlobalTheory_SplitPlace_exists_root
-- name    : GlobalTheory.SplitPlace.exists_root
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:24:50.362563+00:00
-- url     : https://prove2.me/theorems/ab513774-bd6d-5202-82b3-77e827ca9d96
-- title:
--   Split Place: exists root
-- statement:
--   The Split Place construction uses the exists root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NotIsFieldAdicCompletionTensorOfSplit.lean#L9-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NotIsFieldAdicCompletionTensorOfSplit.lean#L9-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NotIsFieldAdicCompletionTensorOfSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain Polynomial
open GlobalTheory GlobalTheory.SplitPlace

theorem GlobalTheory.SplitPlace.exists_root {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (t n : 𝓞 F) (hn : n ∈ v.asIdeal) (ht : t ∉ v.asIdeal) :
    ∃ r : v.adicCompletion F, r ^ 2 + algebraMap F _ (t : F) * r + algebraMap F _ (n : F) = 0 := by sorry
