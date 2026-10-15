-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_eval_of_steps
-- name    : MIPRE.Cost.Machine.eval_of_steps
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:27:50.139246+00:00
-- url     : https://prove2.me/theorems/3667c247-5d46-4994-8c50-6285f77d4f2c
-- title:
--   From machine runs to derivations: a run reaching a final configuration contains a derivation of the same cost
-- statement:
--   The *evaluation machine* (`Machine`) is a small-step, CEK-style machine for the ambient language of the cost model. A configuration $\langle \kappa, \rho, k \rangle$ (`Cfg`) consists of a control $\kappa$, which is either $\mathtt{ev}\,p$ ("evaluate the program $p$") or $\mathtt{ret}\,v$ ("return the value $v$"), an environment $\rho$ (a list of data, variable $0$ first) and a stack $k$ of continuation frames: $\mathtt{cons1}(t, \rho)$ (the head of a $\mathtt{cons}$ is being evaluated; evaluate $t$ in $\rho$ next), $\mathtt{cons2}(a)$ (the head value is $a$; return $\mathtt{cons}(a, \cdot)$ next), $\mathtt{let1}(b, \rho)$ and $\mathtt{loop1}(b, \rho)$. The step function $\mathrm{step}$ (`step`) is total and deterministic, and it leaves *final* configurations $\langle \mathtt{ret}\,v, \rho, [] \rangle$ unchanged. Each configuration is charged a cost $\mathrm{stepCost}$: a configuration $\langle \mathtt{ev}\,p, \rho, k\rangle$ is charged the unit of the evaluation rule for the head constructor of $p$ — $\mathrm{size}(\rho(i)) + 1$ for $\mathtt{var}\ i$, $1$ for $\mathtt{nil}$, $\mathrm{size}(d)$ for $\mathtt{const}\ d$, $1$ for $\mathtt{cons}$, $\mathtt{elim}$ and $\mathtt{let}$, and $0$ for $\mathtt{loop}$, whose unit is charged instead when the value of the body is dispatched at a $\mathtt{loop1}$ frame; all other returns cost $0$. Write $\mathrm{cost}(c, N) = \sum_{i < N} \mathrm{stepCost}(\mathrm{step}^i(c))$ (`costSum`) for the cost accumulated over $N$ steps, and $\mathrm{Steps}(c, N, c', t)$ (`Steps`) for "$\mathrm{step}^N(c) = c'$ and $\mathrm{cost}(c, N) = t$". The big-step semantics $\rho \vdash p \Downarrow_t r$ (`Eval`) is the timed evaluation relation that the machine implements: $p$ in the environment $\rho$ halts with result $r$ at cost $t$.
--
--   **Statement.** Let $N \in \mathbb{N}$, let $p$ be a program, $\rho$ an environment, $k$ a stack, $r$ a datum and $e$ an environment, and suppose
--
--   $$ \mathrm{step}^{N}\langle \mathtt{ev}\,p, \rho, k \rangle = \langle \mathtt{ret}\,r, e, [] \rangle , $$
--
--   that is, the machine started on $p$ reaches a final configuration (a returned value on an empty stack) within $N$ steps. Then there exist a value $r'$, a cost $t$, step counts $M$ and $N'$ with $N = M + N'$, and an environment $\rho'$ such that
--
--   $$ \rho \vdash p \Downarrow_t r' \qquad\text{and}\qquad \mathrm{Steps}\bigl(\langle \mathtt{ev}\,p, \rho, k \rangle,\ M,\ \langle \mathtt{ret}\,r', \rho', k \rangle,\ t\bigr) : $$
--
--   the first $M$ steps of the run return a value $r'$ to the stack $k$ with accumulated cost exactly $t$, and $r'$ is the result of a derivation for $p$ in $\rho$ of that same cost.
--
--   This is the backward direction of the correspondence between derivations and machine runs; with `eval_steps` it yields `halts_iff`. It is what makes the self-interpreter *sound*: a halting run of the universal program is a machine run reaching a final configuration, hence a derivation with the same result (`univProg_halts_of`, blueprint `lem:universal-tm`), and likewise for the clocked variant and for the decision procedure for cost budgets.
--
--   **Formalization Note**: The statement is deliberately in "prefix" form, generalized over the stack $k$ and with $N = M + N'$, so that a strong induction on $N$ goes through the recursive structure of the machine; it does not identify $r'$ with the final value $r$ — that is done in `halts_iff` for $k = []$, using that final configurations are fixed by $\mathrm{step}$. Finality requires an empty stack: a returned value under a non-empty stack is not fixed by the machine.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Machine.lean#L209-L329; internal lemma of the formalization of blueprint lem:universal-tm (via the self-interpreter)

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Machine

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine

theorem MIPRE.Cost.Machine.eval_of_steps : ∀ (N : ℕ) (p : Prog) (env : Env) (k : List Frame) (r : Data) (e : Env),
    step^[N] ⟨.ev p, env, k⟩ = ⟨.ret r, e, []⟩ →
    ∃ r' t M e' N', N = M + N' ∧ Eval env p r' t ∧ Steps ⟨.ev p, env, k⟩ M ⟨.ret r', e', k⟩ t := by sorry
