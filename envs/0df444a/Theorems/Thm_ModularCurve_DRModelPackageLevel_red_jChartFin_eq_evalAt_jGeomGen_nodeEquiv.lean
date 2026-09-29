-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_red_jChartFin_eq_evalAt_jGeomGen_nodeEquiv
-- name    : ModularCurve.DRModelPackageLevel.red_jChartFin_eq_evalAt_jGeomGen_nodeEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/fe59de82-422d-5232-aeb4-99b9f9f36156
-- title:
--   Reduction of the chart value of j at a crossing
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$ and $p$ prime not dividing $N_0$, and a model package $\mathfrak{P}$ of type `DRModelPackageLevel N₀ p hpN₀` for the curve $X(N_0,p)$ over $\operatorname{Spec} R_p$. Let $\kappa$ be an algebraically closed field of characteristic $p$ equipped with a ring homomorphism $\mathrm{to}\kappa : R_p \to \kappa$, let $A$ be a commutative ring with a ring homomorphism $\mathrm{red} : A \to \kappa$, and let $f : \operatorname{Spec} A \to X(N_0,p)$ be a morphism which factors as $\operatorname{Spec}$ of a ring homomorphism $\varphi : \mathrm{chartAlgFin}(N_0p,p) \to A$ followed by the chart morphism `ιFin (N₀ * p) p`, so that $f$ lands in the finite-level Igusa chart. Let $u_\kappa : \operatorname{Spec}\kappa \to \mathrm{fibre}\,\mathrm{to}\kappa$, the fibre being the pullback of the structure morphism `toBase N₀ p` along $\operatorname{Spec}$ of $\mathrm{to}\kappa$, be a morphism whose first projection component is $\operatorname{Spec}$ of $\mathrm{red}$ followed by $f$ and whose second projection component is the identity of $\operatorname{Spec}\kappa$; thus $u_\kappa$ is a $\kappa$-point of the special fibre realising the reduction of $f$ along $\mathrm{red}$. Finally let $n$ be a point of the fibre product of the two morphisms `𝔓.comp κ toκ 0` and `𝔓.comp κ toκ 1`, the package's two components of the special fibre over $\kappa$, so that $n$ is a crossing point, and assume that the image of $n$ under the first projection followed by `𝔓.comp κ toκ 0` is the image of the closed point of $\operatorname{Spec}\kappa$ under $u_\kappa$. The conclusion is that $\mathrm{red}(\varphi(\mathrm{jChartFin}(N_0p,p)))$, the reduction of the value at the given point of the chart generator given by the modular function $j$ at level $N_0p$, equals the value $\mathrm{evalAt}$ of $\mathrm{jGeomGen}\,\kappa\,N_0 = \langle j_q \bmod p \rangle \in \mathrm{modularFunctionFieldC}\,\kappa\,N_0$ at the place $\mathfrak{P}.\mathrm{nodeEquiv}\,\kappa\,\mathrm{to}\kappa\,n$ of $\mathrm{modularFunctionFieldC}\,\kappa\,N_0$ over $\kappa$, which by construction lies in $\mathrm{ssPlaces}\,p\,N_0\,\kappa$, the set of places satisfying $\mathrm{IsSupersingularPlace}$; here $\mathrm{evalAt}$ denotes the residue-field value of an element of the valuation subring of the place (and $0$ for elements outside it).
--
--   This is one half of the dictionary between the special fibre of the Deligne–Rapoport model at $p$ and the supersingular points in characteristic $p$: a point of the Igusa chart whose reduction hits a crossing has $j$-value equal to the $j$-invariant of the supersingular place by which the package labels that crossing. It is used by [`ModularCurve.DRModelPackageLevel.reduceFst_mem_ssPlaces_of_specialPoint_eq_crossing`](thm.html#ModularCurve.DRModelPackageLevel.reduceFst_mem_ssPlaces_of_specialPoint_eq_crossing), which concludes that the first reduction of such a place is supersingular.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_red_jChartFin_eq_evalAt_jGeomGen_nodeEquiv.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_CharPReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel
  ModularCurve.IgusaScheme ModularCurve.PlaceSpecialization

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.DRModelPackageLevel.red_jChartFin_eq_evalAt_jGeomGen_nodeEquiv
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : R p →+* κ)
    {A : Type} [CommRing A] (red : A →+* κ)
    (f : Spec (CommRingCat.of A) ⟶ X N₀ p)
    (φ : ↥(chartAlgFin (N₀ * p) p) →+* A) (hf : f = Spec.map (CommRingCat.ofHom φ) ≫ ιFin (N₀ * p) p)
    (uκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) toκ)
    (h₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom red) ≫ f) (h₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (n : ↥(pullback (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)))
    (hn : (pullback.fst (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1) ≫ 𝔓.comp κ toκ 0).base n =
      uκ.base (IsLocalRing.closedPoint κ)) :
    red (φ (jChartFin (N₀ * p) p)) =
      ((𝔓.nodeEquiv κ toκ n : ↥(ssPlaces p N₀ κ)) : Place κ ↥(modularFunctionFieldC κ N₀)).evalAt (jGeomGen κ N₀) := by sorry
