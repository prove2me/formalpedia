-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_idealSheaf_comap_map_of_stable
-- name    : GlobalTheory.GaloisDescent.idealSheaf_comap_map_of_stable
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:43:11.124903+00:00
-- url     : https://prove2.me/theorems/90ccf4d7-e7d2-4724-85bf-2b3297a65b43
-- title:
--   Galois Descent: ideal Sheaf comap map of stable
-- statement:
--   The Galois Descent construction uses the ideal Sheaf comap map of stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueComapEqVanishingIdeal.lean#L44-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueComapEqVanishingIdeal.lean#L44-L90

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
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.GaloisDescent.idealSheaf_comap_map_of_stable (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (a : G → (Y ⟶ Y)) (haπ : ∀ g, a g ≫ π = π)
    (haq : ∀ g, a g ≫ q = q ≫ Spec.map (CommRingCat.ofHom (s g)))
    (I : Y.IdealSheafData) (hI : ∀ g, I.comap (a g) ≤ I) : (I.map π).comap π = I := by sorry
