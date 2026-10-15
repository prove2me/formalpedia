-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_eval_steps_bound
-- name    : MIPRE.Cost.Machine.eval_steps_bound
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:28:20.015596+00:00
-- url     : https://prove2.me/theorems/d9d7ba7e-63bd-47f3-98d9-d0f5c0fbb830
-- title:
--   Size bounds along the machine run of a derivation: values $\le V$, environments $\le L+2t$, stack $\le K+t$
-- statement:
--   The *evaluation machine* (`MIPRE.Cost.Machine`) is a small-step abstract machine in the style of the CEK machine that implements the timed big-step semantics $\rho \vdash p \Downarrow^{t} r$ (`Eval ρ p r t`: the program $p$, in the environment $\rho$, halts with result $r$ at cost $t$) of the ambient cost model, in which data are binary trees with $\mathrm{size}$ the number of nodes and programs form a first-order language with de Bruijn variables. A *configuration* $\langle \gamma, \rho, \kappa \rangle$ (`Cfg`) consists of a control $\gamma$, which is either $\mathrm{ev}\,p$ ("evaluate the program $p$") or $\mathrm{ret}\,v$ ("return the value $v$"), an environment $\rho$ (a list of values), and a stack $\kappa$ of continuation frames (`Frame`) of four kinds: $\mathrm{cons}_1(q, \rho)$ (the head of a pair is being evaluated; evaluate the tail $q$ in $\rho$ next), $\mathrm{cons}_2(a)$ (the head $a$ has been computed; pair it with the tail's value), $\mathrm{let}_1(b, \rho)$ (the bound expression of a `let` is being evaluated; then run the body $b$ in $\rho$ extended by its value), and $\mathrm{loop}_1(b, \rho)$ (the body $b$ of a loop is being evaluated in $\rho$; then dispatch on its value). The step function $\mathrm{step}$ is total and deterministic, $\mathrm{step}^{n}$ is its $n$-fold iterate, and each step is charged the cost of the evaluation rule it carries out (`stepCost`), the steps that carry out no rule — entering a loop, returning a value to a $\mathrm{cons}_1$, $\mathrm{cons}_2$ or $\mathrm{let}_1$ frame, or a final configuration — being free. We write $\mathrm{Steps}(c, N, c', t)$ (`Steps`) when $\mathrm{step}^{N}(c) = c'$ and the costs of these $N$ steps add up to $t$.
--
--   For $V, L, P, K \in \mathbb{N}$, a configuration $c$ is *bounded*, $\mathrm{CfgBound}(V, L, P, K, c)$, if: a returned value has size at most $V$; a program under evaluation has encoded size at most $P$ (programs are encoded by their syntax trees, $\|p\| = \mathrm{size}(\mathrm{enc}(p))$); the environment has length at most $L$ and each of its values has size at most $V$; the stack has at most $K$ frames; and every frame is bounded in the same sense (`FrameBound`): its program has encoded size at most $P$, its environment has length at most $L$ with values of size at most $V$, and the value of a $\mathrm{cons}_2$ frame has size at most $V$.
--
--   **Theorem.** Let $\rho \vdash p \Downarrow^{t} r$ be a derivation. Then for every stack $\kappa$ and all $V, L, P, K \in \mathbb{N}$ such that the initial configuration $\langle \mathrm{ev}\,p, \rho, \kappa\rangle$ is bounded by $(V, L, P, K)$ and $t \le V$, there exist $N \in \mathbb{N}$ and an environment $\rho'$ such that
--
--   $$
--   \mathrm{Steps}\bigl(\langle \mathrm{ev}\,p, \rho, \kappa\rangle,\ N,\ \langle \mathrm{ret}\,r, \rho', \kappa\rangle,\ t\bigr)
--   \quad\text{and}\quad
--   \forall n \le N:\ \mathrm{CfgBound}\bigl(V,\ L + 2t,\ P,\ K + t,\ \mathrm{step}^{n}\langle \mathrm{ev}\,p, \rho, \kappa\rangle\bigr).
--   $$
--
--   In words: started on $p$ in $\rho$ above the stack $\kappa$, the machine reaches in $N$ steps the configuration that returns $r$ above the same stack $\kappa$, the accumulated cost being exactly the cost $t$ of the derivation, and every configuration visited on the way is bounded with the same value bound $V$ and program bound $P$, an environment-length bound increased by $2t$, and a stack-depth bound increased by $t$.
--
--   This is the central quantitative lemma behind the efficient universal machine of blueprint `lem:universal-tm`. The self-interpreter `univProg` of the ambient model iterates a program implementing $\mathrm{step}$ on encoded configurations, whose cost is polynomial in the size of the configuration; one therefore needs every configuration of the run simulating a halting computation to be small. Combined with `size_toData_le` (the encoded size of a bounded configuration is at most a polynomial in $V, L, P, K$) and `eval_steps_count` (the run has at most $3t$ steps), this lemma yields the polynomial overhead of `univProg` (`UniversalMachine.time_le`) and the size guard of the clocked universal machine `univTProg`. Its variant `eval_steps_bound_forever` extends the bound to all $n$ when $\kappa$ is empty, the final configuration being a fixed point of $\mathrm{step}$.
--
--   **Formalization Note** The hypothesis $t \le V$ is what makes the value bound uniform: every value produced along the run is the result of a sub-derivation of cost at most $t$, hence has size at most $t$ (`Eval.size_le`); the initial values must separately be bounded by $V$ through the hypothesis on the initial configuration. The increments are read off the rules: an `elim` on a pair pushes two values onto the environment at unit cost (whence $2t$), a `let` or a loop iteration pushes one; a `cons`, a `let` or a `loop` pushes one frame at a cost of at least one unit (whence $t$). Programs under evaluation are always subterms of $p$ or of the programs stored in the frames of $\kappa$, so the bound $P$ never grows. The stack $\kappa$ below the run is arbitrary and is returned unchanged, and the final environment $\rho'$ is existentially quantified (the machine restores environments from frames but keeps the bindings made by `elim`, so $\rho'$ may extend $\rho$). The cost in `Steps` is the Lean's `stepCost`, which charges the costs of the `Eval` rules at designated steps so that a run accumulates exactly the cost of the derivation.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/MachineBound.lean#L108-L380; internal lemma of the formalization of blueprint lem:universal-tm (via the self-interpreter), https://vidick.github.io/MIPRE-formalization/blueprint/; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 2.1

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

theorem MIPRE.Cost.Machine.eval_steps_bound {env : Env} {p : Prog} {r : Data} {t : ℕ} (h : Eval env p r t) :
    ∀ (k : List Frame) (V L P K : ℕ), CfgBound V L P K ⟨.ev p, env, k⟩ → t ≤ V →
    ∃ N env', Steps ⟨.ev p, env, k⟩ N ⟨.ret r, env', k⟩ t ∧
      ∀ n ≤ N, CfgBound V (L + 2 * t) P (K + t) (step^[n] ⟨.ev p, env, k⟩) := by sorry
