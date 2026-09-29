-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_exists_coordinate_forall_mem_range_compInf_and_not_mem_range_compZero
-- name    : ModularCurve.DRModelPackage.exists_coordinate_forall_mem_range_compInf_and_not_mem_range_compZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/06de08be-0d19-5684-80f9-9476c5395630
-- title:
--   Ogg's unit detects the ∞-component mod p
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $F =$ `modularFunctionFieldFull p` be the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the $q$-expansions $j(q^d)$ for the divisors $d$ of $p$, and let $\mathfrak{X}$ be a `DRModelPackage p`: a bundle of data and properties for the two-chart integral model `DRModel p`, the pushout over $\operatorname{Spec}\mathbb{Z}$ of the finite-$j$ and infinite-$j$ chart spectra attached to $F$ and to the element `IgusaScheme.jFull p` of $F$, together with its structure morphism `DRModel.toBase p` to $\operatorname{Spec}\mathbb{Z}$, rational and geometric generic curve models, sections, a smooth locus and the component morphisms used below. Assume `hmem`: the Laurent series `modularUnitSeries p`, namely $\Delta(q)$ divided by the $p$-fold $q$-expansion rescaling $\Delta(q^p)$, lies in $F$; write $u \in F$ for the resulting element. Then there is an element $v$ of `HpoolLevelRing.Afin p`, the finite-$j$ chart algebra `chartAlgFin ℤ F (jFull p)` inside $F$, such that (i) the image of $v$ in $F$ is either $u$ or $p^{12} u^{-1}$, and (ii) for every algebraically closed field $k$ of characteristic $p$, every point $y$ of the fibre product of `DRModel.toBase p` with $\operatorname{Spec}$ of $\mathbb{Z} \to k$, and every prime ideal $\mathfrak{q}$ of `HpoolLevelRing.Afin p`, if the first projection of $y$ is the image of $\mathfrak{q}$ under the topological map of the finite chart morphism `TwoChartIntegralModel.ιFin`, and $v \notin \mathfrak{q}$, then $y$ lies in the range of the topological map of `𝔛.compInf k` and not in the range of that of `𝔛.compZero k`.
--
--   This is the arithmetic input of Ogg's argument on the two components of the Deligne–Rapoport model of $X_0(p)$ in characteristic $p$: the modular unit $\Delta(q)/\Delta(q^p)$ (or its Atkin–Lehner companion $p^{12}u^{-1}$) is invertible along one of the two components of the geometric fibre at $p$ and vanishes on the other, so its non-vanishing at a point pins that point to the component carrying the section $\varepsilon_\infty$ and away from the other. It feeds into [`ModularCurve.DRModelPackage.exists_locallySplitPools_of_le_span_prime`](thm.html#ModularCurve.DRModelPackage.exists_locallySplitPools_of_le_span_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_exists_coordinate_forall_mem_range_compInf_and_not_mem_range_compZero.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_HpoolLevelRing
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.DRModelPackage.exists_coordinate_forall_mem_range_compInf_and_not_mem_range_compZero
    (p : ℕ) [Fact p.Prime] [NeZero p] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (hmem : modularUnitSeries p ∈ modularFunctionFieldFull p) :
    ∃ v : HpoolLevelRing.Afin p,
      ((v : ↥(ModularCurve.modularFunctionFieldFull p)) = ⟨modularUnitSeries p, hmem⟩ ∨
        (v : ↥(ModularCurve.modularFunctionFieldFull p)) = (p : ↥(ModularCurve.modularFunctionFieldFull p)) ^ 12 * (⟨modularUnitSeries p, hmem⟩ : ↥(ModularCurve.modularFunctionFieldFull p))⁻¹) ∧
      ∀ (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
        (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) (𝔮 : PrimeSpectrum (HpoolLevelRing.Afin p)),
        (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y =
          (AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(ModularCurve.modularFunctionFieldFull p) (IgusaScheme.jFull p)).base 𝔮 →
        v ∉ 𝔮.asIdeal →
        y ∈ Set.range (𝔛.compInf k).base ∧ y ∉ Set.range (𝔛.compZero k).base := by sorry
