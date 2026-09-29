-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_mem_connectedComponentIn_of_aeval_mem
-- name    : ModularCurve.DRModelPackage.mem_connectedComponentIn_of_aeval_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/445aa840-4144-5b07-9f3b-9b735d3535f8
-- title:
--   Vanishing of g(v) forces membership in the ε_∞-component
-- statement:
--   Let $p$ be a prime and let $\mathfrak X$ be a `DRModelPackage p`, that is, a bundle of data for the two-chart integral model `DRModel p` of the full modular function field of level $p$ over $\operatorname{Spec}\mathbb Z$, with its distinguished open `smoothLocus`, sections `εinf`, `εzero` over $\operatorname{Spec}\mathbb Z$ and geometric-fibre components `compInf`, `compZero`. Let $v$ belong to `HpoolLevelRing.Afin p`, the $j$-finite chart algebra, and assume the hypothesis `hdict`: for every algebraically closed field $k$ of characteristic $p$, every point $y$ of the fibre $\mathfrak X\times_{\mathbb Z}k$ and every prime $\mathfrak q$ of `Afin p` such that the first projection sends $y$ to the image of $\mathfrak q$ under the finite-chart morphism `ιFin` and $v\notin\mathfrak q$, the point $y$ lies in the range of `(𝔛.compInf k).base` and not in the range of `(𝔛.compZero k).base`. Let $g\in\mathbb Z[X]$ have constant coefficient not divisible by $p$, let $f\in\mathbb Z$, let $k$ be an algebraically closed field, let $s\colon\operatorname{Spec}k\to\operatorname{Spec}\mathbb Z[1/f]$, where $\mathbb Z[1/f]$ is `Localization.Away f`, and let $y$ be a point of the fibre over $s$ of the base change of `DRModel.toBase p` to $\mathbb Z[1/f]$. Let $\mathfrak q$ be a prime of `Afin p` such that the composite of the two first projections down to `DRModel p` sends $y$ to the image of $\mathfrak q$ under `ιFin`, and assume $g(v)\in\mathfrak q$. Then $y$ lies in the connected component, inside the preimage of $\mathfrak X$.`smoothLocus` under that composite, of the image of the closed point of $\operatorname{Spec}k$ under the $k$-point of the double pullback obtained from the base change of the section `εinf` to $\mathbb Z[1/f]$ by `sectionFibrePoint`.
--
--   Geometric fibre by geometric fibre, this places the zero set of a pool coordinate $g(v)$ on the $j$-finite chart into the connected component of the cusp section $\varepsilon_\infty$ within the smooth locus of the Deligne–Rapoport model of $X_0(p)$ over $\mathbb Z[1/f]$, the characteristic-$p$ case resting on the dictionary hypothesis identifying such points with points of the $\infty$-component off the $0$-component. It supplies the component clause in the construction of locally split pools, [`ModularCurve.DRModelPackage.exists_locallySplitPools_of_le_span_prime`](thm.html#ModularCurve.DRModelPackage.exists_locallySplitPools_of_le_span_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_mem_connectedComponentIn_of_aeval_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_ModularCurve_HpoolLevelRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.RelPicard

theorem ModularCurve.DRModelPackage.mem_connectedComponentIn_of_aeval_mem
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (v : HpoolLevelRing.Afin p)
    (hdict : ∀ (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
      (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))))
      (𝔮 : PrimeSpectrum (HpoolLevelRing.Afin p)),
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y =
        (AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(ModularCurve.modularFunctionFieldFull p) (IgusaScheme.jFull p)).base 𝔮 →
      v ∉ 𝔮.asIdeal →
      y ∈ Set.range (𝔛.compInf k).base ∧ y ∉ Set.range (𝔛.compZero k).base)
    (g : Polynomial ℤ) (hg0 : ¬ (p : ℤ) ∣ g.coeff 0) (f : ℤ)
    (k : Type) [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
    (y : ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
    (𝔮 : PrimeSpectrum (HpoolLevelRing.Afin p))
    (hy : (pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫
        pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))).base y =
      (AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(ModularCurve.modularFunctionFieldFull p) (IgusaScheme.jFull p)).base 𝔮)
    (hg : Polynomial.aeval v g ∈ 𝔮.asIdeal) :
    y ∈ connectedComponentIn
      (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
          (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
      (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k)) := by sorry
