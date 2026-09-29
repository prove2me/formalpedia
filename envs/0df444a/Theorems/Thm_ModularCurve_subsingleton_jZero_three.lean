-- Prove2me | Theorems.Thm_ModularCurve_subsingleton_jZero_three
-- name    : ModularCurve.subsingleton_jZero_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/9a97a617-a92b-5316-adc9-f51ef258e60d
-- title:
--   Triviality of J₀(3)
-- statement:
--   The assertion is that the type `JZero 3` is a subsingleton, i.e. has at most one element. Here `JZero N` is defined as `Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N)`, where `modularFunctionFieldBar N` is the base change to $\overline{\mathbb Q}$, inside the field of Laurent series over $\overline{\mathbb Q}$, of the intermediate field `modularFunctionFieldFull N` of $\mathbb Q$-Laurent series — the level-$N$ modular function field, realised through $q$-expansions. For a field extension $F/K$, `Pic0 K F` is the quotient of the additive group of divisors of degree zero of $F/K$ by the subgroup of principal divisors contained in it. Thus, instantiated at $N = 3$, the statement says that the degree-zero divisor class group of the level-$3$ modular function field over $\overline{\mathbb Q}$ has at most one element; since it is a quotient group, this is the statement that every divisor of degree zero of that function field is principal, i.e. that $J_0(3) = 0$. The theorem takes no variables and no hypotheses.
--
--   This is the statement that the Jacobian of $X_0(3)$ is trivial, $X_0(3)$ being a curve of genus zero. It is used in the level-$3$ instances of results about $J_0(q)$ (prolongation pairs, fixed parts of kernels of specialisation maps) and in the collected statement [`ModularCurve.subsingleton_jZero_of_lt_five`](thm.html#ModularCurve.subsingleton_jZero_of_lt_five).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_subsingleton_jZero_three.lean

import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.subsingleton_jZero_three : Subsingleton (JZero 3) := by sorry
