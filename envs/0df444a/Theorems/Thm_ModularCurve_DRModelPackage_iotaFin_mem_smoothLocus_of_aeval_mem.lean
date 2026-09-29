-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_iotaFin_mem_smoothLocus_of_aeval_mem
-- name    : ModularCurve.DRModelPackage.iotaFin_mem_smoothLocus_of_aeval_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/d6591470-62f4-526c-8267-df17ae68ae24
-- title:
--   Zeros of g(v) in the finite chart lie in the smooth locus
-- statement:
--   Let $p$ be a prime and let $\mathfrak X$ be a `DRModelPackage p`, i.e. a package of data for the two-chart integral model `DRModel p` $=$ `TwoChartIntegralModel ℤ (modularFunctionFieldFull p) (IgusaScheme.jFull p)` over $\operatorname{Spec}\mathbb Z$ (properness, flatness and integrality of `DRModel.toBase p`, integral closedness of the sections over affine opens, curve models of the rational and geometric generic fibres with their compatibilities, two sections `εinf`, `εzero` over $\operatorname{Spec}\mathbb Z$, and a distinguished open `smoothLocus` that is smooth of relative dimension $1$ over the base and contains every open that is smooth over the base). Let $v$ be an element of `HpoolLevelRing.Afin p`, the ring of the $j$-finite chart, namely the $\mathbb Z$-subalgebra `chartAlgFin` of `modularFunctionFieldFull p` attached to `IgusaScheme.jFull p`. Assume the hypothesis `hdict`: for every algebraically closed field $k$ of characteristic $p$, every point $y$ of the pullback of `DRModel.toBase p` along $\operatorname{Spec}$ of $\mathbb Z\to k$, and every prime $\mathfrak q$ of `HpoolLevelRing.Afin p`, if the first projection of $y$ is the image of $\mathfrak q$ under the finite-chart morphism `ιFin` and $v\notin\mathfrak q$, then $y$ lies in the range of the underlying map of $\mathfrak X$`.compInf k` and not in the range of that of $\mathfrak X$`.compZero k`. Let $g\in\mathbb Z[X]$ with $p\nmid g(0)$, i.e. $p$ does not divide the coefficient of $g$ in degree $0$, and let $\mathfrak q$ be a prime of `HpoolLevelRing.Afin p` with $g(v)\in\mathfrak q$ (the evaluation of $g$ at $v$ as an algebra map from $\mathbb Z[X]$). Then the image of $\mathfrak q$ under `ιFin` lies in the open $\mathfrak X$`.smoothLocus` of `DRModel p`.
--
--   This is the step, in the description of the reduction of $X_0(p)$ at $p$ due to Deligne and Rapoport, which says that a point of the $j$-finite chart cut out by a monic-free integral relation $g(v)=0$ with $p\nmid g(0)$ cannot be a supersingular crossing point: geometric points above it lie on the $\infty$-component and off the $0$-component, hence in the smooth locus. It is used in [`ModularCurve.DRModelPackage.exists_locallySplitPools_of_le_span_prime`](thm.html#ModularCurve.DRModelPackage.exists_locallySplitPools_of_le_span_prime), and its proof cites [`ModularCurve.DRModelPackage.mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_compInf`](thm.html#ModularCurve.DRModelPackage.mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_compInf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_iotaFin_mem_smoothLocus_of_aeval_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_ModularCurve_HpoolLevelRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve AlgebraicGeometry.RelPicard

theorem ModularCurve.DRModelPackage.iotaFin_mem_smoothLocus_of_aeval_mem
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (v : HpoolLevelRing.Afin p)
    (hdict : ∀ (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
      (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))))
      (𝔮 : PrimeSpectrum (HpoolLevelRing.Afin p)),
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y =
        (AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(ModularCurve.modularFunctionFieldFull p) (IgusaScheme.jFull p)).base 𝔮 →
      v ∉ 𝔮.asIdeal →
      y ∈ Set.range (𝔛.compInf k).base ∧ y ∉ Set.range (𝔛.compZero k).base)
    (g : Polynomial ℤ) (hg0 : ¬ (p : ℤ) ∣ g.coeff 0)
    (𝔮 : PrimeSpectrum (HpoolLevelRing.Afin p)) (hg : Polynomial.aeval v g ∈ 𝔮.asIdeal) :
    (AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(ModularCurve.modularFunctionFieldFull p) (IgusaScheme.jFull p)).base 𝔮 ∈ 𝔛.smoothLocus := by sorry
