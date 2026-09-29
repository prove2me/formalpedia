-- Prove2me | Theorems.Thm_ModularCurve_kaehlerRankOne_modularFunctionFieldC_of_isSeparable_jqNModC
-- name    : ModularCurve.kaehlerRankOne_modularFunctionFieldC_of_isSeparable_jqNModC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/a7025ead-5ae0-5899-a013-546a127be290
-- title:
--   Rank-one Kähler differentials of K(j(q),j(q^N))
-- statement:
--   Let $K$ be a field and $N$ a natural number with $N \neq 0$. Inside the field $\mathrm{LaurentSeries}\,K$ of formal Laurent series over $K$, write $j =$ `jqModC K` for the series $q^{-1}$ times the image under $\mathbb{Z} \to K$ of the power series `jNum` $= E_4^3 \cdot \eta^{-24}$ (so $j$ is the $q$-expansion of the modular invariant, with leading term $q^{-1}$), and write $j_N =$ `jqNModC K N` for its image under the ring homomorphism `qExpand K N`, which multiplies all Hahn-series exponents by $N$, i.e. substitutes $q \mapsto q^N$. Assume that $j_N$ is separable over the intermediate field $K(j)$ obtained by adjoining $\{j\}$ to $K$ in $\mathrm{LaurentSeries}\,K$, i.e. that the minimal polynomial of $j_N$ over $K(j)$ is a separable polynomial. The conclusion concerns the field $F =$ `modularFunctionFieldC K N`, the intermediate field $K(j, j_N)$ of $\mathrm{LaurentSeries}\,K$ generated over $K$ by $j$ and $j_N$: the module of Kähler differentials $\Omega_{F/K}$ is a free $F$-module, and its $F$-rank equals $1$.
--
--   This is the transcendence-degree-one, or rank-one differentials, input for treating $K(j, j_N)$ as the function field of a curve over $K$: the classical statement that for a separably generated function field of one variable the module of differentials is free of rank one. It is used in the computation of $q$-expansions of differentials on modular curves and of their traces and pullbacks under the Hecke correspondences, for instance by [`ModularCurve.coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC`](thm.html#ModularCurve.coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC) and [`ModularCurve.hasse_smul_traceAlong_smul_pullbackAlong_smul_D_jGeomGen_eq`](thm.html#ModularCurve.hasse_smul_traceAlong_smul_pullbackAlong_smul_D_jGeomGen_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_kaehlerRankOne_modularFunctionFieldC_of_isSeparable_jqNModC.lean

import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve KaehlerDifferential
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.kaehlerRankOne_modularFunctionFieldC_of_isSeparable_jqNModC
    (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (hsep : IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (jqNModC K N)) :
    Module.Free (modularFunctionFieldC K N) Ω[(modularFunctionFieldC K N)⁄K]
      ∧ Module.finrank (modularFunctionFieldC K N) Ω[(modularFunctionFieldC K N)⁄K] = 1 := by sorry
