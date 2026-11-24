-- Prove2me | Theorems.Thm_GlobalTheory_HopfQuot_sum_lam
-- name    : GlobalTheory.HopfQuot.sum_lam
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:37:46.949115+00:00
-- url     : https://prove2.me/theorems/c938e9e2-063f-42fe-a815-5cd4a065377e
-- title:
--   Hopf Quot: sum lam
-- statement:
--   The Hopf Quot construction uses the sum lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L170-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteFaithfullyFlatKer.lean#L170-L202

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

theorem GlobalTheory.HopfQuot.sum_lam (e : ι → Λ) (c : ι → Λ →ₗ[R] R)
    (h : ∀ m, ∑ i, c i m • e i = m) (x : Λ) :
    ∑ k, lam e c (c k) (HopfAlgebra.antipode R (e k) * x) = Coalgebra.counit (R := R) x := by sorry
