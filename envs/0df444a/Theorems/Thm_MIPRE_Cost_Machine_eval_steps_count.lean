-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_eval_steps_count
-- name    : MIPRE.Cost.Machine.eval_steps_count
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:28:35.801983+00:00
-- url     : https://prove2.me/theorems/4e87e335-2562-4166-8eb1-55b0a61c5558
-- title:
--   The machine run of a derivation of cost $t$ takes at most $3t$ steps
-- statement:
--   The evaluation machine (`MIPRE.Cost.Machine`) implements the timed big-step semantics $\rho \vdash p \Downarrow^{t} r$ (`Eval ρ p r t`: the program $p$ in the environment $\rho$ halts with result $r$ at cost $t$) of the ambient cost model by small steps on configurations $\langle \gamma, \rho, \kappa\rangle$, where the control $\gamma$ is $\mathrm{ev}\,p$ ("evaluate $p$") or $\mathrm{ret}\,v$ ("return $v$"), $\rho$ is an environment and $\kappa$ a stack of continuation frames ($\mathrm{cons}_1$, $\mathrm{cons}_2$, $\mathrm{let}_1$, $\mathrm{loop}_1$; see `eval_steps_bound`). Each step is charged the cost of the evaluation rule it carries out (`stepCost`) — reading a variable or a literal costs the size of the value (plus one for a variable), the other rules one unit — and the steps that carry out no rule are free: entering a loop, and returning a value to a $\mathrm{cons}_1$, $\mathrm{cons}_2$ or $\mathrm{let}_1$ frame or to the empty stack. $\mathrm{Steps}(c, N, c', t)$ (`Steps`) means that $N$ steps lead from $c$ to $c'$ with total cost $t$.
--
--   **Theorem.** Let $\rho \vdash p \Downarrow^{t} r$ be a derivation and $\kappa$ any stack. Then there exist $N \in \mathbb{N}$ and an environment $\rho'$ such that
--
--   $$
--   \mathrm{Steps}\bigl(\langle \mathrm{ev}\,p, \rho, \kappa\rangle,\ N,\ \langle \mathrm{ret}\,r, \rho', \kappa\rangle,\ t\bigr) \qquad\text{and}\qquad N \le 3t.
--   $$
--
--   That is, the machine simulates the derivation above any stack, with accumulated cost exactly $t$, in at most $3t$ steps.
--
--   The theorem sharpens the simulation lemma `eval_steps` (which gives the run without the bound on $N$) with the step count needed for the time analysis of the self-interpreter. In the universal program `univProg` each machine step is one iteration of the interpreter loop, so a simulated computation of cost $t$ takes at most $3t$ iterations, each on a configuration whose encoded size is bounded through `eval_steps_bound` and `size_toData_le`; this is the polynomial time overhead of the efficient universal machine, blueprint `lem:universal-tm`. In the clocked universal machine `univTProg`, $3k + 1$ is the step budget that guarantees termination of a simulation with cost budget $k$.
--
--   **Formalization Note** Every rule of the semantics has positive cost (`Eval.pos`; a literal $d$ costs $\mathrm{size}(d) \ge 1$), so a derivation of cost $t$ involves at most $t$ paid steps, and the factor $3$ comes from the free steps: each is matched with the paid step that pushed the corresponding frame — the two returns of a pair with its `cons` step, the return of a `let`'s bound value with its `let` step, the entry of a loop with the dispatch step at its $\mathrm{loop}_1$ frame — and a paid step has at most two free companions. The bound is in terms of the derivation cost $t$ alone, independent of the sizes of the program or of the environment. The stack $\kappa$ is arbitrary and returned unchanged, and the final environment $\rho'$ is existentially quantified. The cost $t$ in $\mathrm{Steps}$ is the sum of the Lean's `stepCost` over the run, which the theorem asserts equals the cost of the derivation.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/MachineBound.lean#L472-L532; internal lemma of the formalization of blueprint lem:universal-tm (via the self-interpreter), https://vidick.github.io/MIPRE-formalization/blueprint/; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 2.1

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine

theorem MIPRE.Cost.Machine.eval_steps_count {env : Env} {p : Prog} {r : Data} {t : ℕ} (h : Eval env p r t)
    (k : List Frame) :
    ∃ N env', Steps ⟨.ev p, env, k⟩ N ⟨.ret r, env', k⟩ t ∧ N ≤ 3 * t := by sorry
