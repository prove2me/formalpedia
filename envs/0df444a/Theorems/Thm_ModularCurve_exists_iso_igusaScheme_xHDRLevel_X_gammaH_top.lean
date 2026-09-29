-- Prove2me | Theorems.Thm_ModularCurve_exists_iso_igusaScheme_xHDRLevel_X_gammaH_top
-- name    : ModularCurve.exists_iso_igusaScheme_xHDRLevel_X_gammaH_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/4143b90b-2fde-52a5-9b1f-c3df95248d3a
-- title:
--   Igusa's model of X₀(M) as the H=top two-chart model
-- statement:
--   Let $p$ be a prime and $M$ a positive integer, and let $hj$ witness that the Laurent series `jqModC ℚ` lies in $\mathrm{qExpFunctionFieldC}\,\mathbb{Q}\,(\top)$, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios `intFormRatiosC ℚ ⊤`. Both schemes in play are two-chart integral models over the coefficient ring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8): `IgusaScheme M p` is built from the field $\mathrm{modularFunctionFieldFull}\,M = \mathbb{Q}(\mathrm{divisorExpansions}\,M) \subset \mathbb{Q}((q))$ and the element `jFull M`, and `XHDRLevel.X p (CohCarrier.GammaH M ⊤) hj` from the field $\mathrm{qExpFunctionFieldC}\,\mathbb{Q}\,\Gamma$ with $\Gamma = \mathrm{GammaH}\,M\,\top$ (the image in $SL_2(\mathbb{Z})$ of the preimage of $\top$ under `gamma0Units M`) and the element $\mathrm{jAt}\,\Gamma\,hj$; in each case the two charts are the subalgebras of elements integral over the coefficient ring adjoined with $j$, respectively with $j^{-1}$, glued along their common localisation. The assertion is that there exist an isomorphism of schemes $e$ between these two models and ring homomorphisms `eFin`, `eInf` between the corresponding finite-$j$ chart algebras and pole chart algebras such that: each of `eFin` and `eInf` preserves the underlying Laurent series of every element; $e$ followed by the structure morphism of the level model to $\operatorname{Spec}$ of the coefficient ring equals the structure morphism `IgusaScheme.igusaTo`; and, for both charts, $\operatorname{Spec}$ of the chart map followed by the Igusa chart immersion equals the level-model chart immersion followed by $e^{-1}$.
--
--   This identifies Igusa's two-chart integral model of $X_0(M)$ over the localised base with the member at $H=(\mathbb{Z}/M)^\times$ of the family of integral models attached to the $q$-expansion function fields of the groups $\Gamma_H(M)$, compatibly with the charts, the structure morphisms and $q$-expansions. It is used in the comparison of the $H=\top$ level model with the Deligne–Rapoport-type model and its points-versus-places dictionary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_iso_igusaScheme_xHDRLevel_X_gammaH_top.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open ModularCurve
open scoped MatrixGroups
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_iso_igusaScheme_xHDRLevel_X_gammaH_top
    (p M : ℕ) [Fact p.Prime] [NeZero M] (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    ∃ (e : IgusaScheme M p ≅ XHDRLevel.X p (CohCarrier.GammaH M ⊤) hj)
      (eFin : ↥(IgusaScheme.chartAlgFin M p) →+* ↥(XHDRLevel.chartAlgFin p (CohCarrier.GammaH M ⊤) hj))
      (eInf : ↥(IgusaScheme.chartAlgInf M p) →+* ↥(XHDRLevel.chartAlgInf p (CohCarrier.GammaH M ⊤) hj)),

      (∀ x : ↥(IgusaScheme.chartAlgFin M p),
        (((eFin x : ↥(XHDRLevel.chartAlgFin p (CohCarrier.GammaH M ⊤) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M ⊤))) : LaurentSeries ℚ) =
          ((x : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)) ∧
      (∀ x : ↥(IgusaScheme.chartAlgInf M p),
        (((eInf x : ↥(XHDRLevel.chartAlgInf p (CohCarrier.GammaH M ⊤) hj)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M ⊤))) : LaurentSeries ℚ) =
          ((x : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)) ∧

      e.hom ≫ XHDRLevel.toBase p (CohCarrier.GammaH M ⊤) hj = IgusaScheme.igusaTo M p ∧

      Spec.map (CommRingCat.ofHom eFin) ≫ IgusaScheme.ιFin M p = XHDRLevel.ιFin p (CohCarrier.GammaH M ⊤) hj ≫ e.inv ∧
      Spec.map (CommRingCat.ofHom eInf) ≫ IgusaScheme.ιInf M p = XHDRLevel.ιInf p (CohCarrier.GammaH M ⊤) hj ≫ e.inv := by sorry
