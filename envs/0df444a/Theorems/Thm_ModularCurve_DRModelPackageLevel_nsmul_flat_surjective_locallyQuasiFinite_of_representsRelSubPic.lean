-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_nsmul_flat_surjective_locallyQuasiFinite_of_representsRelSubPic
-- name    : ModularCurve.DRModelPackageLevel.nsmul_flat_surjective_locallyQuasiFinite_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/e8d18abe-e422-533b-b446-5df389ff6685
-- title:
--   Multiplication by n on relative Pic⁰: flat, surjective, quasi-finite
-- statement:
--   Fix an integer $N_0 \ge 1$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak P$ be a level-$N_0p$ Deligne–Rapoport package `DRModelPackageLevel N₀ p hpN₀`, whose data include the structure morphism `toBase N₀ p` from the curve `X N₀ p` to $\operatorname{Spec}$ of the ring `R p` together with the section $\varepsilon_\infty$ over the identity of the base. Let $D$ be a `RelativePic0Designation` for this morphism, that is, a scheme $D.P$ with a morphism $D.\mathrm{toBase}$ to the base and a section of it. Assume $hD$: $D$ represents the subfunctor of rigidified line bundles on `X N₀ p` (rigidified along $\varepsilon_\infty$) cut out by the condition that the bundle be algebraically equivalent to zero on every geometric fibre, i.e. there is a Poincaré rigidified bundle on $D.\mathrm{toBase}$ satisfying that condition, every rigidified bundle satisfying it over any base scheme is the pullback of the Poincaré bundle along a unique morphism over the base, and the zero section pulls the Poincaré bundle back to the unit. Assume further that $D.\mathrm{toBase}$ is smooth and that each of its set-theoretic fibres is preconnected. Then for the relative group law on $D.\mathrm{toBase}$ obtained from $hD$ via the tensor- and inverse-stable form of that fibrewise condition, the multiplication-by-$n$ morphism $[n] : D.P \to D.P$ is flat, surjective and locally quasi-finite for every $n > 0$.
--
--   This is the package-level form, for $\Gamma_0(N_0p)$ over the base ring `R p`, of the statement that multiplication by $n$ on the identity component of the relative Picard scheme of a Deligne–Rapoport model is an fppf epimorphism with quasi-finite kernel; it is one of the group-theoretic properties required of the level-$N_0p$ Néron object, and it feeds into the construction of that object together with the bridge identifying it with the representing scheme of relative $\mathrm{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_nsmul_flat_surjective_locallyQuasiFinite_of_representsRelSubPic.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.nsmul_flat_surjective_locallyQuasiFinite_of_representsRelSubPic
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    [Smooth D.toBase]
    (hconn : ∀ s : Spec (CommRingCat.of (R p)), _root_.IsPreconnected (D.toBase.base ⁻¹' {s})) :
    (∀ n : ℕ, 0 < n →
      Flat ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase N₀ p) 𝔓.εinf) hD).schemeNsmul n)) ∧
    (∀ n : ℕ, 0 < n →
      Surjective ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase N₀ p) 𝔓.εinf) hD).schemeNsmul n)) ∧
    (∀ n : ℕ, 0 < n →
      LocallyQuasiFinite
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase N₀ p) 𝔓.εinf) hD).schemeNsmul n)) := by sorry
