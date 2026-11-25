-- Prove2me | Theorems.Thm_GlobalTheory_KS_isCob_of_mixed
-- name    : GlobalTheory.KS.isCob_of_mixed
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:58:09.054563+00:00
-- url     : https://prove2.me/theorems/0697ad5b-5ba3-43e9-ab72-35f9f60f9da7
-- title:
--   KS: is Cob of mixed
-- statement:
--   The KS construction uses the is Cob of mixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsCechOneCoboundaryOfMixedOverlaps.lean#L11-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsCechOneCoboundaryOfMixedOverlaps.lean#L11-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCechOneCoboundaryOfMixedOverlaps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
noncomputable section
open GlobalTheory GlobalTheory.KS

theorem GlobalTheory.KS.isCob_of_mixed : ∀ (X : Scheme.{0}) (J K : Type) (V : J → X.Opens) (U : K → X.Opens), ⨆ k, U k = ⊤ → ∀ (z : C1 V) (z' : C1 U) (b : ∀ i k, Γ(X, V i ⊓ U k)), (∀ i i' k, rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (b i k) (V i ⊓ V i' ⊓ U k) - rsT (b i' k) (V i ⊓ V i' ⊓ U k)) → (∀ i k k', rsT (z' k k') (V i ⊓ U k ⊓ U k') = rsT (b i k') (V i ⊓ U k ⊓ U k') - rsT (b i k) (V i ⊓ U k ⊓ U k')) → IsCob U z' → IsCob V z := by sorry
