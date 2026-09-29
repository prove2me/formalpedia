-- Prove2me | Theorems.Thm_NeronModelInfra_exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints
-- name    : NeronModelInfra.exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/650e99df-2abd-5237-81c0-ff93c434f723
-- title:
--   Existence of ω-minimal component data over a discrete valuation ring
-- statement:
--   Let $R$ be a discrete valuation ring with fraction field $K$, and let $g_K\colon X_K \to \operatorname{Spec} K$ be smooth, separated, locally of finite type and quasi-compact. Assume given: a relative group law `LXK` on $g_K$, i.e. a group structure on the sections of $g_K$ over every $K$-scheme $T \to \operatorname{Spec} K$, natural in $T$ for multiplication; a model family $M$ over $R$, consisting of a type $\iota$ of indices, schemes $X_i$ with structure morphisms $X_i \to \operatorname{Spec} R$ and open immersions (charts) of the generic fibre $X_i \times_{\operatorname{Spec} R} \operatorname{Spec} K$ into $X_K$ over $K$, with $\iota$ finite and each structure morphism smooth, separated, locally of finite type and quasi-compact; the hypothesis that $M$ catches index-one points, i.e. for every discrete valuation ring $R'$ that is a local $R$-algebra with fraction field $K'$ compatible with $K$, such that the maximal ideal of $R$ generates that of $R'$ and the residue field extension is formally smooth, every $K'$-point of $g_K$ comes, via a chart, from an $R'$-point of some $X_i$; a natural number $d$ with $g_K$ smooth of relative dimension $d$; and a global section $\omega$ of the $d$-th determinant $\bigwedge^{d}$ of the relative Kähler module of $g_K$ which is a frame on the whole space, that is, multiplication by the restriction of $\omega$ is a bijection $\Gamma(X_K,W) \to \Gamma(\bigwedge^{d}\Omega,W)$ for every open $W$. The conclusion asserts the existence of minimal component data $D$ for $(R,K,g_K,d,\omega)$ which is $\omega$-minimal. Here minimal component data consist of a finite non-empty index type together with component readings $C(c)$ — each a smooth, locally of finite type $R$-scheme $Y \to \operatorname{Spec} R$ with an open immersion of its generic fibre into $X_K$, a point $y$ over the closed point of $\operatorname{Spec} R$ maximal for specialisation among such points, a discrete valuation ring stalk at $y$ which is an $R$-algebra compatibly with $f$ and whose fraction field is a $K$-algebra in a scalar tower, a basis of $\Omega$ of the stalk over $R$ indexed by $\mathrm{Fin}\,d$, an affine open of $X_K$ with the corresponding algebra structures, and further reading data including a numerical invariant $n$ — subject to: each $C(c)$ has separated and quasi-compact structure morphism, the chart of $C(c)$ is an isomorphism onto $X_K$, every point of $Y$ over the closed point is a specialisation of $y$, and distinct indices give readings that are inequivalent near their marked points. $\omega$-minimality says that $n$ of each $C(c)$ is least among all component readings $T$ for $(R,K,g_K,d,\omega)$, and that every $T$ attaining this minimal value of $n$ is realised by some $C(c)$: there are an open neighbourhood $W$ of $T.y$ and a morphism $W \to (C(c)).Y$ over $\operatorname{Spec} R$ which is an open immersion, carries $T.y$ to the marked point of $C(c)$, and is compatible with the two charts on generic fibres.
--
--   This is the existence of $\omega$-minimal component data attached to a weak Néron model of a smooth separated quasi-compact $K$-group scheme, as in Bosch–Lütkebohmert–Raynaud, 4.3. It is the input to the construction of a model of $X_K$ over $R$ to which all translations extend near the marked points, used by [`NeronModelInfra.exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative`](thm.html#NeronModelInfra.exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_NeronModelInfra_OmegaMinimalComponentData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite GoodReductionJacobian
open AlgebraicGeometry
open NeronModelInfra

universe u

theorem NeronModelInfra.exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (M : ModelFamily R K gK) (hfin : Finite M.ι)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i))
    (hpts : M.CatchesIndexOnePoints)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤)) (hω : Scheme.Modules.IsFrameOn ω ⊤) :
    ∃ D : MinimalComponentData R K gK d ω, D.IsOmegaMinimal := by sorry
