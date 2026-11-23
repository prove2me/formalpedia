-- Prove2me | Theorems.Thm_GlobalTheory_HopfQuot_tr_comm
-- name    : GlobalTheory.HopfQuot.tr_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:28.044164+00:00
-- url     : https://prove2.me/theorems/2c0640c9-0227-459e-bf4f-971269c5bc44
-- title:
--   Hopf Quot: tr comm
-- statement:
--   The Hopf Quot construction uses the tr comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L13-L23

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
variable {A M ι : Type*} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι]

theorem GlobalTheory.HopfQuot.tr_comm (e : ι → M) (c : ι → M →ₗ[A] A) (h : ∀ m, ∑ i, c i m • e i = m)
    (φ ψ : M →ₗ[A] M) : tr e c (φ ∘ₗ ψ) = tr e c (ψ ∘ₗ φ) := by sorry
