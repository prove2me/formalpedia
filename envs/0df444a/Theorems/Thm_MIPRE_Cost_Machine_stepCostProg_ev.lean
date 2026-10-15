-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_stepCostProg_ev
-- name    : MIPRE.Cost.Machine.stepCostProg_ev
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:42.396283+00:00
-- url     : https://prove2.me/theorems/e110fe28-c620-476f-8f4c-0f378aeb53e5
-- title:
--   The step-cost program on an evaluate-configuration reduces to the case program selected by the constructor tag
-- statement:
--   The clocked self-interpreter needs, at each simulated step, the exact cost $\mathsf{stepCost}(c)$ that the evaluation machine charges for the step from the configuration $c$; the program `stepCostProg` computes it, in unary, from the encoding $\lceil c\rceil$. On a configuration in evaluation mode, "evaluate $p$", the cost depends only on the constructor of $p$ and on its arguments: it is $1 + \mathrm{size}$ of the variable's value for $\mathsf{var}\,i$, $\mathrm{size}(d)$ for $\mathsf{const}\,d$, $1$ for $\mathsf{nil}$, $\mathsf{cons}$, $\mathsf{elim}$ and $\mathsf{let}$, and $0$ for $\mathsf{loop}$. Accordingly `stepCostProg` takes the configuration apart and dispatches on the unary constructor tag $k \in \{0, \dots, 6\}$ of the program to one of seven fixed *case programs* $\mathtt{costCases}_k$ (tags $0$ to $6$ standing for $\mathsf{var}$, $\mathsf{nil}$, $\mathsf{cons}$, $\mathsf{elim}$, $\mathsf{let}$, $\mathsf{loop}$, $\mathsf{const}$), each of which receives the pair (payload of $p$, encoded environment) as its input.
--
--   Let $k < 7$, let $\mathit{body}$ (the payload of a program with tag $k$), $\mathit{env}$ (an encoded environment), $\mathit{kont}$ (an encoded stack) and $r$ be values, and let $t \in \mathbb{N}$. Suppose that the $k$-th case program, run on the single input $\mathsf{cons}\;\mathit{body}\;\mathit{env}$, halts with result $r$ at cost $t$. Then there is a cost
--   $$ s \le t + 2\,\mathrm{size}(\mathit{body}) + 2\,\mathrm{size}(\mathit{env}) + \mathrm{size}(\mathit{kont}) + k + 14 $$
--   such that `stepCostProg`, run on the encoded evaluate-configuration
--   $$ \mathsf{cons}\;\bigl(\mathsf{cons}\;\mathsf{nil}\;(\mathsf{cons}\;(\mathsf{ofNat}\,k)\;\mathit{body})\bigr)\;(\mathsf{cons}\;\mathit{env}\;\mathit{kont}) $$
--   (control "evaluate the program with tag $k$ and payload $\mathit{body}$", environment $\mathit{env}$, stack $\mathit{kont}$) halts with the same result $r$ at cost $s$.
--
--   This is the common prefix of all seven evaluate-cases of the correctness theorem `stepCostProg_runs`, which then only has to run each case program on its pair. It serves the clocked universal machine of blueprint `lem:universal-tm`.
--
--   **Formalization Note**: The case programs are the list `costCases` of `Cost/Universal.lean`, indexed with `List.getD` (default $\mathsf{nil}$, never reached since $k < 7$); the overhead $k$ in the bound is the cost of walking the dispatch chain, one $\mathsf{elim}$ per tag. The hypothesis is a run in the one-element environment $[\mathsf{cons}\;\mathit{body}\;\mathit{env}]$ (the case programs are closed), and the conclusion is a run in the one-element environment holding the encoded configuration, that is, a `Prog.Runs` statement spelled out.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Universal.lean#L525-L550; internal lemma of the formalization of blueprint lem:universal-tm, https://vidick.github.io/MIPRE-formalization/blueprint/

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

theorem MIPRE.Cost.Machine.stepCostProg_ev (k : ℕ) (body env kont r : Data) {t : ℕ}
    (hk : k < costCases.length)
    (h : Eval [Data.cons body env] (costCases.getD k .nil) r t) :
    ∃ s ≤ t + 2 * body.size + 2 * env.size + kont.size + k + 14,
      Eval [Data.cons (.cons .nil (.cons (.ofNat k) body)) (.cons env kont)] stepCostProg r s := by sorry
