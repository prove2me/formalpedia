-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_eval_steps
-- name    : MIPRE.Cost.Machine.eval_steps
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:27:51.19298+00:00
-- url     : https://prove2.me/theorems/eb6df8c7-b7fb-4e47-9a36-9a240d95b601
-- title:
--   From derivations to machine runs: the evaluation machine simulates a run of cost $t$ at accumulated cost exactly $t$
-- statement:
--   The *evaluation machine* (`Machine`) is a small-step, CEK-style machine for the ambient language of the cost model. A configuration $\langle \kappa, \rho, k \rangle$ (`Cfg`) consists of a control $\kappa$, which is either $\mathtt{ev}\,p$ ("evaluate the program $p$") or $\mathtt{ret}\,v$ ("return the value $v$"), an environment $\rho$ (a list of data, variable $0$ first) and a stack $k$ of continuation frames: $\mathtt{cons1}(t, \rho)$ (the head of a $\mathtt{cons}$ is being evaluated; evaluate $t$ in $\rho$ next), $\mathtt{cons2}(a)$ (the head value is $a$; return $\mathtt{cons}(a, \cdot)$ next), $\mathtt{let1}(b, \rho)$ and $\mathtt{loop1}(b, \rho)$. The step function $\mathrm{step}$ (`step`) is total and deterministic, and it leaves *final* configurations $\langle \mathtt{ret}\,v, \rho, [] \rangle$ unchanged. Each configuration is charged a cost $\mathrm{stepCost}$: a configuration $\langle \mathtt{ev}\,p, \rho, k\rangle$ is charged the unit of the evaluation rule for the head constructor of $p$ — $\mathrm{size}(\rho(i)) + 1$ for $\mathtt{var}\ i$, $1$ for $\mathtt{nil}$, $\mathrm{size}(d)$ for $\mathtt{const}\ d$, $1$ for $\mathtt{cons}$, $\mathtt{elim}$ and $\mathtt{let}$, and $0$ for $\mathtt{loop}$, whose unit is charged instead when the value of the body is dispatched at a $\mathtt{loop1}$ frame; all other returns cost $0$. Write $\mathrm{cost}(c, N) = \sum_{i < N} \mathrm{stepCost}(\mathrm{step}^i(c))$ (`costSum`) for the cost accumulated over $N$ steps, and $\mathrm{Steps}(c, N, c', t)$ (`Steps`) for "$\mathrm{step}^N(c) = c'$ and $\mathrm{cost}(c, N) = t$". The big-step semantics $\rho \vdash p \Downarrow_t r$ (`Eval`) is the timed evaluation relation that the machine implements: $p$ in the environment $\rho$ halts with result $r$ at cost $t$.
--
--   **Statement.** If $\rho \vdash p \Downarrow_t r$, then for every stack $k$ there are a step count $N$ and an environment $\rho'$ such that
--
--   $$ \mathrm{step}^{N}\langle \mathtt{ev}\,p, \rho, k \rangle = \langle \mathtt{ret}\,r, \rho', k \rangle \qquad\text{and}\qquad \mathrm{cost}\bigl(\langle \mathtt{ev}\,p, \rho, k \rangle, N\bigr) = t . $$
--
--   This is the forward direction of the correspondence between derivations and machine runs; with the converse `eval_of_steps` it gives `halts_iff`. The machine is the common core of the two universal artifacts of the formalization: the self-interpreter that realizes the efficient universal machine (blueprint `lem:universal-tm`), whose time bound starts from this simulation (refined to $N \le 3t$ steps in `eval_steps_count`), and the proof that evaluation is partial recursive (`mem_evalData_iff`).
--
--   **Formalization Note**: The machine does not restore environments on return — `elim` extends the environment in place and a `loop1` dispatch replaces it — so the environment $\rho'$ at the return is existentially quantified, while the stack $k$ is restored exactly. The cost identity is exact, by the choice of `stepCost` matching the evaluation rules one for one. The statement is about the machine on `Cfg`, before configurations are encoded as data.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Machine.lean#L143-L202; internal lemma of the formalization of blueprint lem:universal-tm (via the self-interpreter)

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

theorem MIPRE.Cost.Machine.eval_steps {env : Env} {p : Prog} {r : Data} {t : ℕ} (h : Eval env p r t)
    (k : List Frame) :
    ∃ N env', Steps ⟨.ev p, env, k⟩ N ⟨.ret r, env', k⟩ t := by sorry
