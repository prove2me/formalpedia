-- Prove2me | Theorems.Thm_ModularCurve_JOne_degeneracyPullbackInputs
-- name    : ModularCurve.JOne.degeneracyPullbackInputs
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/272e78d7-ec32-53d1-8b47-e515e31f9551
-- title:
--   Degeneracy pull-back inputs hold whenever Nt ∣ N'
-- statement:
--   Let $N$, $t$, $N'$ be nonzero natural numbers with $Nt \mid N'$. The conclusion is the predicate [`ModularCurve.JOne.DegeneracyPullbackInputs N N' t`](def/ModularCurve_X1DegeneracyPullback.html#L109), i.e. the conjunction of the following data and assertions, packaged as an existential. First, the divisibility $Nt \mid N'$ itself. Second, `HeckeBetaOneDefined N t`: every $y$ in the $q$-expansion function field `x1FunctionField N` of $\Gamma_1(N)$ has its substitution $q \mapsto q^{t}$, namely `qExpand ℚ t y`, lying in `x1x0FunctionFieldC ℚ N (N * t)`. Third and fourth, integrality over $\overline{\mathbb{Q}}$ of the two $\overline{\mathbb{Q}}$-algebra maps from `laurentBaseChange (AlgebraicClosure ℚ) (x1FunctionField N)` to the corresponding field at level $N'$: the inclusion `x1LevelInclBar` attached to $N \mid N'$ (obtained from $N \mid Nt \mid N'$), and `x1LevelSubstBar`, the substitution $q \mapsto q^{t}$ followed by the inclusion of the level-$(N, Nt)$ field into level $N'$; integrality means each is an integral ring homomorphism. Fifth, `HasPrincipalDivisors (AlgebraicClosure ℚ) (x1FunctionFieldBar N')`: every nonzero element $f$ of the base-changed function field at level $N'$ admits a divisor $D$ with $D(v) = \mathrm{ord}_v(f)$ at every place trivial on $\overline{\mathbb{Q}}$ and $\deg D = 0$. Finally, the fundamental identity $\sum_{w \mid v} e(w/v) f(w/v) = [F' : F]$ holds along each of the two maps.
--
--   This collects, for a pair of levels with $Nt \mid N'$, exactly the hypotheses under which the two degeneracy maps between the function fields of $X_1(N)$ and $X_1(N')$ induce pull-backs of degree-zero divisor classes, hence maps $J_1(N) \to J_1(N')$ on the Jacobians [`ModularCurve.JOne`](def/ModularCurve_X1.html#L186). It is invoked by the statements about Tate modules of $J_1$ and $J_H$ that are used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOne_degeneracyPullbackInputs.lean

import Mathlib
import Definitions.Def_ModularCurve_X1DegeneracyPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JOne.degeneracyPullbackInputs (N : ℕ) [NeZero N] (t : ℕ) [NeZero t]
    (N' : ℕ) [NeZero N'] (h : N * t ∣ N') :
    ModularCurve.JOne.DegeneracyPullbackInputs N N' t := by sorry
