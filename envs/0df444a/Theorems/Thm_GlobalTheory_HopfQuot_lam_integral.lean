-- Prove2me | Theorems.Thm_GlobalTheory_HopfQuot_lam_integral
-- name    : GlobalTheory.HopfQuot.lam_integral
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:37:33.543434+00:00
-- url     : https://prove2.me/theorems/54a1db28-afb2-4d1c-9500-7ebc8bb34412
-- title:
--   Hopf Quot: lam integral
-- statement:
--   The Hopf Quot construction uses the lam integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L130-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L130-L168

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HopfQuot
open TensorProduct
variable {R Λ ι : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Fintype ι]

theorem GlobalTheory.HopfQuot.lam_integral [Module.Finite R Λ] (e : ι → Λ) (c : ι → Λ →ₗ[R] R)
    (h : ∀ m, ∑ i, c i m • e i = m) (f : Λ →ₗ[R] R) (x : Λ) :
    ev Λ (lam e c f) (Coalgebra.comul x) = algebraMap R Λ (lam e c f x) := by sorry
