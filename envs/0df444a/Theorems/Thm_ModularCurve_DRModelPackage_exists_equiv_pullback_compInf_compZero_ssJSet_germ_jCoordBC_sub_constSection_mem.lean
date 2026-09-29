-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_exists_equiv_pullback_compInf_compZero_ssJSet_germ_jCoordBC_sub_constSection_mem
-- name    : ModularCurve.DRModelPackage.exists_equiv_pullback_compInf_compZero_ssJSet_germ_jCoordBC_sub_constSection_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/63d2d8db-4fb0-5a6b-9c24-b4fb0ebb7782
-- title:
--   Crossings of the mod p fibre have supersingular j-invariants
-- statement:
--   Let $p$ be a prime with $p\ge 5$, let $\mathfrak X$ be a Deligne–Rapoport model package for level $p$ (a structure packaging the integral model `DRModel p` together with its properness, flatness, integrality and normality, the rational and geometric curve models with their compatibilities, the two sections $\varepsilon_\infty,\varepsilon_0$, the smooth locus, and the further data of the structure), and let $k$ be an algebraically closed field of characteristic $p$ with decidable equality. Write $C_\infty = \mathfrak X.\mathrm{compInf}\,k$ and $C_0 = \mathfrak X.\mathrm{compZero}\,k$ for the two morphisms from $(\mathfrak X.\mathrm{ratModel}\,k).C$ into the base change of `DRModel.toBase p` along $\mathbb Z\to k$, i.e. into `TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k`. The assertion is that there is a bijection $a$ from the underlying set of the scheme-theoretic fibre product of $C_\infty$ and $C_0$ onto $\mathrm{ssJSet}\,p\,k$, the set of $j\in k$ such that every elliptic Weierstrass curve $W$ over $k$ with $W.j=j$ has trivial $p$-torsion on its affine model ($p\cdot P=0$ implies $P=0$), with the following property: for every point $n$ of the fibre product, the image $y_n$ of $n$ under the first projection followed by $C_\infty$ lies in the open subscheme `chartFinOpenBC` (the preimage of the finite chart under the base-change map), and the germ at $y_n$ of `jCoordBC` minus the restriction to that chart of the constant section `constSection` with value $a(n)\in k$ lies in the maximal ideal of the local ring at $y_n$.
--
--   This is the Deligne–Rapoport description of the geometric fibre at $p$ of the integral model of $X_0(p)$ for $p\ge5$: the two components cross exactly at the supersingular points, and the crossings are enumerated by the supersingular $j$-invariants, the $j$-coordinate of the crossing indexed by $n$ being $a(n)$. It feeds the corresponding statement for the resolved model package, [`ModularCurve.DRResolvedModelPackage.exists_node_equiv_ssJSet_germ_sub_mem_maximalIdeal_iff`](thm.html#ModularCurve.DRResolvedModelPackage.exists_node_equiv_ssJSet_germ_sub_mem_maximalIdeal_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_exists_equiv_pullback_compInf_compZero_ssJSet_germ_jCoordBC_sub_constSection_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.DRModelPackage.exists_equiv_pullback_compInf_compZero_ssJSet_germ_jCoordBC_sub_constSection_mem
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k] :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ a : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)) ≃ ↥(ssJSet p k),
      ∀ n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)),
        ∃ hy : (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n ∈
            TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k,
          ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ
                (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k)
                ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k).base n) hy).hom
              (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k -
                ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.map (homOfLE le_top).op).hom
                  (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k (((a n : ↥(ssJSet p k)) : k)))) ∈
            IsLocalRing.maximalIdeal _ := by sorry
