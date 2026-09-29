-- Prove2me | Theorems.Thm_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4
-- name    : ModularCurve.DRResolvedModelPackage.eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/79cc687f-17a1-502d-b032-9a0c48fe897d
-- title:
--   Euler characteristic of ι_w^*𝒪(Cᵥ) shifts by adjacency number
-- statement:
--   Fix a prime $p$, a package $\mathfrak{X} : \mathtt{DRModelPackage } p$, a commutative ring $O$, an algebraically closed field $\kappa$ of characteristic $p$ with a ring homomorphism $toκ : O \to \kappa$, and a resolved model $R$ of type `DRResolvedModelPackage p 𝔛 O κ toκ`; in particular $R$ provides a scheme $Y$ proper and flat over $\operatorname{Spec} O$, a finite index type $R.\mathrm{node}$ with widths $R.\mathrm{width} : R.\mathrm{node} \to \mathbb{N}$, and for each $v$ in $\mathrm{X0MqComponents}(R.\mathrm{width}) = \mathrm{Fin}\,2 \oplus \bigl(\Sigma\, n,\ \mathrm{Fin}(R.\mathrm{width}\,n - 1)\bigr)$ an invertible ideal sheaf datum $R.\mathrm{comp}\,v$ on $Y$ with closed subscheme $(R.\mathrm{comp}\,v).\mathrm{subscheme}$ and closed immersion $(R.\mathrm{comp}\,v).\mathrm{subschemeι}$. Let $v \neq w$ be two such indices, let $k$ be a field and $y : (R.\mathrm{comp}\,w).\mathrm{subscheme} \to \operatorname{Spec} k$ a proper morphism, and assume the rationality hypothesis: for every node $n$ and every $d : \mathrm{Fin}(R.\mathrm{width}\,n)$ such that $\{v,w\}$ is, in either order, $\{\mathrm{chainPos}\,n\,d, \mathrm{chainPos}\,n\,(d+1)\}$ (where $\mathrm{chainPos}\,n\,d$ is $\mathrm{inl}\,0$ for $d = 0$, $\mathrm{inr}\,\langle n, d-1\rangle$ for $0 < d < R.\mathrm{width}\,n$, and $\mathrm{inl}\,1$ otherwise), there is a section $s$ of $y$, i.e. $s$ followed by $y$ is the identity of $\operatorname{Spec} k$, whose composite with $(R.\mathrm{comp}\,w).\mathrm{subschemeι}$ has the point $R.\mathrm{edgePt}\,n\,d$ in the range of its underlying map. Finally let $\mathcal{W}$ be a pair of affine opens $U_0, U_1$ of $(R.\mathrm{comp}\,w).\mathrm{subscheme}$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. The conclusion compares two two-chart Čech Euler characteristics over $k$, each formed as $\dim_k \ker(\text{Čech differential}) - \dim_k \bigl(\Gamma(U_0 \sqcap U_1) / \operatorname{im}(\text{Čech differential})\bigr)$ for the sections of a module on $(R.\mathrm{comp}\,w).\mathrm{subscheme}$ relative to $y$ and $\mathcal{W}$: for the pullback along $(R.\mathrm{comp}\,w).\mathrm{subschemeι}$ of $(R.\mathrm{comp}\,v).\mathrm{invModule}$, the dual of the module of the ideal sheaf $R.\mathrm{comp}\,v$, it equals the Euler characteristic of the monoidal unit module on $(R.\mathrm{comp}\,w).\mathrm{subscheme}$ plus the integer $\mathrm{x0MqAdj}(R.\mathrm{width})(v,w)$, which is the number of nodes of width $1$ when $v, w$ are the two distinct elements of $\mathrm{Fin}\,2$, is $1$ when one of $v, w$ is $\mathrm{inl}\,0$ and the other is $\mathrm{inr}\,\langle n, 0\rangle$, or one is $\mathrm{inl}\,1$ and the other is $\mathrm{inr}\,\langle n, R.\mathrm{width}\,n - 2\rangle$, or both lie over the same node with consecutive indices, and is $0$ otherwise.
--
--   This is the off-diagonal intersection computation on the resolved model: for distinct components $C_v, C_w$ of the special fibre, the degree of $\mathcal{O}_Y(C_v)$ restricted to $C_w$, read off as the shift in the two-chart Čech Euler characteristic, is the number of points in which the two components meet, as recorded by the adjacency table `x0MqAdj` of the resolved $X_0(p)$ configuration. It feeds the computation of Euler characteristics of strict transforms, via [`ModularCurve.DRResolvedModelPackage.eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective`](thm.html#ModularCurve.DRResolvedModelPackage.eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4.lean

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry ModularCurve

theorem ModularCurve.DRResolvedModelPackage.eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4
    (p : ℕ) [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O]
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ} (R : DRResolvedModelPackage p 𝔛 O κ toκ)
    (v w : X0MqComponents R.width) (hvw : v ≠ w)
    {k : Type} [Field k] (y : (R.comp w).subscheme ⟶ Spec (CommRingCat.of k)) [IsProper y]
    (hrat : ∀ (n : R.node) (d : Fin (R.width n)),
      (v = DRResolvedModelPackage.chainPos R.width n d ∧ w = DRResolvedModelPackage.chainPos R.width n (d + 1)) ∨
          (w = DRResolvedModelPackage.chainPos R.width n d ∧ v = DRResolvedModelPackage.chainPos R.width n (d + 1)) →
      ∃ s : Spec (CommRingCat.of k) ⟶ (R.comp w).subscheme,
        s ≫ y = 𝟙 _ ∧ R.edgePt n d ∈ Set.range (s ≫ (R.comp w).subschemeι).base)
    (𝒲 : ((R.comp w).subscheme).TwoAffineOpenCover) :
    (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp w).subschemeι).obj (R.comp v).invModule)).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp w).subschemeι).obj (R.comp v).invModule)).H1
      = (Module.finrank k (𝒲.sectionsOf y (𝟙_ ((R.comp w).subscheme).Modules)).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y (𝟙_ ((R.comp w).subscheme).Modules)).H1
        + (x0MqAdj R.width v w : ℤ) := by sorry
