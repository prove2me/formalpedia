-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_stepCostProg_runs
-- name    : MIPRE.Cost.Machine.stepCostProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:59.992783+00:00
-- url     : https://prove2.me/theorems/ef3ab1fe-fcea-4396-bd44-b0250d1e7a3f
-- title:
--   `stepCostProg` computes the exact cost of a machine step, in time quadratic in the configuration size
-- statement:
--   The evaluation machine of the ambient cost model charges at each step the cost $\mathsf{stepCost}(c)$ of the evaluation rule it implements ($1 + \mathrm{size}$ of the value read for a variable, $\mathrm{size}(d)$ for a literal $d$, one unit for $\mathsf{nil}$, $\mathsf{cons}$, $\mathsf{elim}$, $\mathsf{let}$ and for the dispatch of a loop body's value, and $0$ otherwise), so that the charges along a run add up to the cost of the big-step derivation. The clocked self-interpreter must decrement its cost budget by exactly this amount at each simulated step; `stepCostProg` is the fixed program of the model that computes it from the encoded configuration, returning it as a unary numeral $\mathsf{ofNat}(\cdot)$.
--
--   For every configuration $c$ there is a cost
--   $$ t \le \mathtt{stepCostBound}\bigl(\mathrm{size}(\lceil c\rceil)\bigr), \qquad \mathtt{stepCostBound}(S) = (S+1)(7S + 32) + 13S + 50, $$
--   such that `stepCostProg`, run on the single input $\lceil c\rceil$ (the encoding `Cfg.toData c`), halts with result
--   $$ \mathsf{ofNat}\bigl(\mathsf{stepCost}(c)\bigr) $$
--   at cost $t$.
--
--   The theorem is one of the two programs iterated by the clocked universal machine of blueprint `lem:universal-tm` (the other being the step program `stepProg`); its exactness is what makes the simulated budget agree with the true cost (`clockLoop_runs`, `clockRun_eq`), so that the clocked machine returns the result precisely when the simulated program halts within cost $k$.
--
--   **Formalization Note**: The bound is quadratic rather than linear because of the $\mathsf{var}$ case, where the value of variable $i$ is located by walking the encoded environment (`getListProg`, which copies the remainder of the environment at each of its steps) and its size is then computed in unary (`sizeProg`, quadratic in the size of the value). The constants of `stepCostBound` are those produced by the proof, with no attempt at optimality; only polynomiality matters downstream (`stepCostPoly`).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Universal.lean#L576-L786; internal lemma of the formalization of blueprint lem:universal-tm, https://vidick.github.io/MIPRE-formalization/blueprint/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open Polynomial
open MIPRE.Cost.Prog

theorem MIPRE.Cost.Machine.stepCostProg_runs (c : Cfg) :
    ∃ t ≤ stepCostBound (Cfg.toData c).size,
      stepCostProg.Runs c.toData (.ofNat (stepCost c)) t := by sorry
