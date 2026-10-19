-- Prove2me | Theorems.Thm_MazurTransfer_exists_preimage_same_reduction_of_smooth_endomorphism_henselian
-- name    : MazurTransfer.exists_preimage_same_reduction_of_smooth_endomorphism_henselian
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-16T14:49:40.8556+00:00
-- url     : https://prove2.me/theorems/4fe05391-d230-458d-be93-3c1664f493e0
-- title:
--   Lifting preimages with prescribed reduction over a henselian local ring
-- statement:
--   Let $R$ be a henselian local commutative ring with residue field $k$, and let $X$ be an $R$-scheme. Suppose $e,x\in X(R)$ are sections and $h:X\to X$ is a smooth $R$-endomorphism fixing $e$. If $x$ and $e$ have the same reduction in $X(k)$, then there is a section $z\in X(R)$ satisfying
--
--   $$h(z)=x,\qquad \bar z=\bar e.$$
--
--   Thus $h$ is surjective on the set of sections reducing to $e$. This assertion concerns an arbitrary henselian local ring; it requires neither completeness nor an algebraically closed residue field.
-- source:
--   Original corollary via a smooth fibre product, using AlgebraicGeometry.Smooth.exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing; Anthropic FLT, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
universe u

theorem MazurTransfer.exists_preimage_same_reduction_of_smooth_endomorphism_henselian
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (e x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (h : SchemeHomOver f f) [Smooth h.1]
    (heh : e.1 ≫ h.1 = e.1)
    (hred : Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) ≫ x.1 =
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) ≫ e.1) :
    ∃ z : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f,
      z.1 ≫ h.1 = x.1 ∧
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) ≫ z.1 =
        Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) ≫ e.1 := by sorry
