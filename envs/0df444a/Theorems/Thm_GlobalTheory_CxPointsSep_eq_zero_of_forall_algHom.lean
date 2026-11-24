-- Prove2me | Theorems.Thm_GlobalTheory_CxPointsSep_eq_zero_of_forall_algHom
-- name    : GlobalTheory.CxPointsSep.eq_zero_of_forall_algHom
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:32:29.820814+00:00
-- url     : https://prove2.me/theorems/d4e26953-68e4-4d9f-b9f7-45c22d48d836
-- title:
--   Cx Points Sep: eq zero of forall alg Hom
-- statement:
--   The Cx Points Sep construction uses the eq zero of forall alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfForallAlgHom.lean#L9-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfForallAlgHom.lean#L9-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfForallAlgHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CxPointsSep

theorem GlobalTheory.CxPointsSep.eq_zero_of_forall_algHom {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [IsReduced A] [Algebra.FiniteType k A] (a : A) (h : ∀ e : A →ₐ[k] k, e a = 0) : a = 0 := by sorry
