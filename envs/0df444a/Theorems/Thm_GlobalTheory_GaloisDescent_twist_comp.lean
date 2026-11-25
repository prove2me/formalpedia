-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_twist_comp
-- name    : GlobalTheory.GaloisDescent.twist_comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:53.06214+00:00
-- url     : https://prove2.me/theorems/4ad25c51-4ce2-5f9b-b626-fa7ded00ae32
-- title:
--   Galois Descent: twist comp
-- statement:
--   The Galois Descent construction uses the twist comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueComapEqVanishingIdeal.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueComapEqVanishingIdeal.lean#L126-L130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueComapEqVanishingIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace GlobalTheory.QCoh.Qcqs
universe u
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L : Type u} [Field K] [Field L] [Algebra K L] {X Y : Scheme.{u}}
  {p : X ⟶ Spec (.of K)} {q : Y ⟶ Spec (.of L)} {π : Y ⟶ X}
  (H : IsPullback π q p (Spec.map (CommRingCat.ofHom (algebraMap K L)))) {G : Type*}
include H

theorem GlobalTheory.GaloisDescent.twist_comp (σ τ : L →ₐ[K] L) : twist H (σ.comp τ) = twist H σ ≫ twist H τ := by sorry
