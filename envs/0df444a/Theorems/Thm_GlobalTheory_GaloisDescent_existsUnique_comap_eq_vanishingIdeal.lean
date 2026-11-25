-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_existsUnique_comap_eq_vanishingIdeal
-- name    : GlobalTheory.GaloisDescent.existsUnique_comap_eq_vanishingIdeal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:26.072135+00:00
-- url     : https://prove2.me/theorems/d19762d0-c63f-4171-96d0-1d2a2535be2d
-- title:
--   Galois Descent: exists Unique comap eq vanishing Ideal
-- statement:
--   The Galois Descent construction uses the exists Unique comap eq vanishing Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueComapEqVanishingIdeal.lean#L143-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueComapEqVanishingIdeal.lean#L143-L153

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

theorem GlobalTheory.GaloisDescent.existsUnique_comap_eq_vanishingIdeal (s : G → L →ₐ[K] L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L)) (Z : Closeds Y)
    (hZ : ∀ g, ∀ y ∈ Z, twist H (s g) y ∈ Z) :
    ∃! J : X.IdealSheafData, J.comap π = Scheme.IdealSheafData.vanishingIdeal Z := by sorry
