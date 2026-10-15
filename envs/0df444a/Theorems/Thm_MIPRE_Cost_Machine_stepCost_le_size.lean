-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_stepCost_le_size
-- name    : MIPRE.Cost.Machine.stepCost_le_size
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:30:01.014154+00:00
-- url     : https://prove2.me/theorems/0282f722-28c9-4418-9754-c2d84f2a499c
-- title:
--   The cost charged at a machine step is at most the size of the encoded configuration
-- statement:
--   The evaluation machine of the ambient cost model charges, at each of its steps, the cost of the evaluation rule that the step implements: from a configuration $c$ in evaluation mode the charge $\mathsf{stepCost}(c)$ is $1 + \mathrm{size}(\rho(i))$ for a program $\mathsf{var}\,i$ (the value is copied), $\mathrm{size}(d)$ for $\mathsf{const}\,d$, $1$ for $\mathsf{nil}$, $\mathsf{cons}$, $\mathsf{elim}$ and $\mathsf{let}$, and $0$ for $\mathsf{loop}$; from a configuration in return mode it is $1$ when the top frame is a `loop1` frame (the loop rule is charged when the body's value is dispatched) and $0$ otherwise. Summing these charges along a run reproduces exactly the cost of the big-step derivation.
--
--   For every configuration $c$,
--   $$ \mathsf{stepCost}(c) \le \mathrm{size}(\lceil c\rceil) , $$
--   where $\lceil c\rceil$ is the data encoding `Cfg.toData c` of the configuration.
--
--   The lemma is a bookkeeping step of the clocked universal machine (blueprint `lem:universal-tm`): the clocked loop subtracts $\mathsf{stepCost}(c)$ from its remaining budget with the unary subtraction program, whose cost is quadratic in its arguments, and this inequality lets that cost be bounded in terms of the size guard $\Theta$ on configurations alone.
--
--   **Formalization Note**: `stepCost` is the function of `Cost/Machine.lean`; the encoding $\lceil c\rceil$ contains the encoded environment as a $\mathsf{cons}$-chain, so the size of any environment entry is dominated by it, and the program $\mathsf{const}\,d$ is encoded as $\mathsf{cons}\,(\mathsf{ofNat}\,6)\,d$, so $\mathrm{size}(d)$ is dominated as well. The inequality holds with no hypothesis on $c$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Universal.lean#L552-L574; internal lemma of the formalization of blueprint lem:universal-tm, https://vidick.github.io/MIPRE-formalization/blueprint/

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

theorem MIPRE.Cost.Machine.stepCost_le_size (c : Cfg) : stepCost c ≤ (Cfg.toData c).size := by sorry
