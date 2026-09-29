-- Prove2me | Theorems.Thm_ModularCurve_ramificationIndex_igusaFunctionFieldX1C_eq_one_of_not_evalAt_mem_ssJSet
-- name    : ModularCurve.ramificationIndex_igusaFunctionFieldX1C_eq_one_of_not_evalAt_mem_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/e11bbabd-a753-51f3-8099-0a2e08c12bd8
-- title:
--   Igusa cover of X₁(M) unramified off supersingular places
-- statement:
--   Let $p$ be a prime, let $M$ be a non-zero natural number with $5 \le M$ and $p \nmid M$, and let $\Omega$ be an algebraically closed field of characteristic $p$. Let $w$ be an integral weight-one form for $\Gamma_1(M)$ over $\Omega$: a weight-one modular form on $\Gamma_1(M)$ together with a power series over $\mathbb{Z}$ which is its $q$-expansion, whose reduction `intSeriesC` $\Omega$ is a non-zero Laurent series. Put $K_0 =$ `x1FunctionFieldC` $\Omega\,M$, the intermediate field of $\Omega((q))$ generated over $\Omega$ by the ratios of integral forms for $\Gamma_1(M)$, and let `igusaFunctionFieldX1C` $\Omega\,M\,w$ be the field generated over $\Omega$ by $K_0$ together with $w$'s Hasse root function, the inverse of the reduced series of $w$; $K_0$ is contained in it, and the inclusion makes the larger field a $K_0$-algebra. Let $jIg$ be an element of the larger field whose underlying Laurent series is `jqModC` $\Omega$, namely $q^{-1}$ times the reduction of the power series $E_4^3\cdot\eta$-unit-inverse. Then for every place $P$ of the Igusa field over $\Omega$ — a valuation subring containing $\Omega$, not the whole field, and a principal ideal ring — such that it is *not* the case both that $jIg$ lies in the valuation subring of $P$ and that the residue $P(jIg) \in \Omega$ lies in `ssJSet` $p\,\Omega$ (the set of $j \in \Omega$ such that every elliptic Weierstrass curve over $\Omega$ with invariant $j$ has trivial $p$-torsion), the ramification index of $P$ over $K_0$ — the least $n > 0$ for which some non-zero $f \in K_0$ has $\operatorname{ord}_P f = n$ — equals $1$.
--
--   This is the statement that the Igusa cover of $X_1(M)$ in characteristic $p$ is unramified at every place at which the $j$-invariant either has a pole or takes an ordinary value, ramification being confined to the supersingular places. It feeds the Riemann–Hurwitz computation relating the genus of the Igusa function field to that of the function field of $X_1(M)$ and the number of supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ramificationIndex_igusaFunctionFieldX1C_eq_one_of_not_evalAt_mem_ssJSet.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CongruenceSubgroup
open ModularCurve
open AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.ramificationIndex_igusaFunctionFieldX1C_eq_one_of_not_evalAt_mem_ssJSet
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
    (w : ModularCurve.IntegralWeightOneForm Ω M)
    (jIg : ↥(ModularCurve.igusaFunctionFieldX1C Ω M w)) (hjIg : (jIg : LaurentSeries Ω) = ModularCurve.jqModC Ω) :
    letI : Algebra ↥(ModularCurve.x1FunctionFieldC Ω M) ↥(ModularCurve.igusaFunctionFieldX1C Ω M w) :=
      (IntermediateField.inclusion (ModularCurve.x1FunctionFieldC_le_igusaFunctionFieldX1C Ω M w)).toRingHom.toAlgebra
    ∀ P : AlgebraicCurve.Place Ω ↥(ModularCurve.igusaFunctionFieldX1C Ω M w),
      ¬ (jIg ∈ P.toValuationSubring ∧ P.evalAt jIg ∈ ModularCurve.ssJSet p Ω) →
        P.ramificationIndex ↥(ModularCurve.x1FunctionFieldC Ω M) = 1 := by sorry
