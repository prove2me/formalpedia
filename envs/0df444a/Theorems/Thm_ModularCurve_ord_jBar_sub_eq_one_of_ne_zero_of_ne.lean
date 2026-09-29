-- Prove2me | Theorems.Thm_ModularCurve_ord_jBar_sub_eq_one_of_ne_zero_of_ne
-- name    : ModularCurve.ord_jBar_sub_eq_one_of_ne_zero_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/8450c858-176d-5738-8be9-66023ec86976
-- title:
--   Order one for jmath̄ - c when c ≠ 0, 1728
-- statement:
--   Fix $N \in \mathbb{N}$, nonzero. Let $\overline{F}_N$ denote [`ModularCurve.modularFunctionFieldBar N`](def/ModularCurve_ArithmeticGalois.html#L111), the intermediate field of $\overline{\mathbb{Q}}$ inside the Laurent series field $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ obtained by adjoining to $\overline{\mathbb{Q}}$ the image, under the coefficientwise ring map `coeffEmb` induced by $\mathbb{Q} \to \overline{\mathbb{Q}}$, of `modularFunctionFieldFull N` (the subfield of $\mathrm{LaurentSeries}(\mathbb{Q})$ generated over $\mathbb{Q}$ by the divisor expansions attached to level $N$). Let $v$ be a place of $\overline{F}_N$ over $\overline{\mathbb{Q}}$ in the sense of the project's `Place` structure: a valuation subring of $\overline{F}_N$ containing the image of $\overline{\mathbb{Q}}$, distinct from the whole field, and a principal ideal ring; its `ord` is minus the logarithm of the associated adic valuation, an integer. Let $c \in \overline{\mathbb{Q}}$ with $c \neq 0$ and $c \neq 1728$, and let $\bar\jmath =$ `jBar N`, the element of $\overline{F}_N$ given by the coefficientwise image of the $q$-expansion of the modular invariant. Assume $\mathrm{ord}_v(\bar\jmath - c) > 0$, where $c$ is viewed in $\overline{F}_N$ via the structure map. Then $\mathrm{ord}_v(\bar\jmath - c) = 1$.
--
--   This is the statement that the $j$-map $X_0(N)_{\overline{\mathbb{Q}}} \to X(1)_{\overline{\mathbb{Q}}}$ is unramified over every finite $j$-value other than the two elliptic values $0$ and $1728$, phrased as a vanishing order of $\bar\jmath - c$ at a place. It is used in the genus computation for $\overline{F}_N$ ([`ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula`](thm.html#ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula)), where the sum of local contributions to the differential $d\bar\jmath$ must be confined to the fibres over $0$, $1728$ and the cusp, and in the analysis of place specialisations and of regular differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_jBar_sub_eq_one_of_ne_zero_of_ne.lean

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_jBar_sub_eq_one_of_ne_zero_of_ne (N : ℕ) [NeZero N]
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N))
    (c : AlgebraicClosure ℚ) (hc0 : c ≠ 0) (hc1728 : c ≠ 1728)
    (hpos : 0 < v.ord (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) c)) :
    v.ord (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) c) = 1 := by sorry
