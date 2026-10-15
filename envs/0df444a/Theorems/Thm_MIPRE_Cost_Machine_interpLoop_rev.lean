-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_interpLoop_rev
-- name    : MIPRE.Cost.Machine.interpLoop_rev
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:28.023974+00:00
-- url     : https://prove2.me/theorems/c4dddc05-5941-404d-9025-9fe5c455b925
-- title:
--   The interpreter loop halts only along a machine run that reaches a final configuration with the same value
-- statement:
--   Let `interpBody` be the body of the self-interpreter's loop: on the encoding $\lceil c\rceil$ of a configuration $c$ of the evaluation machine it stops with the returned value if $c$ is final, and otherwise continues with $\lceil\mathsf{step}(c)\rceil$. The lemma is the converse of `interpLoop_runs`: a halting run of the loop can only come from the machine.
--
--   Let $t \in \mathbb{N}$, let $c$ be a configuration, $\rho$ an environment and $r$ a value. If
--   $$ \mathsf{Eval}\;(\lceil c\rceil :: \rho)\;(\mathsf{loop}\;\mathtt{interpBody})\;r\;t , $$
--   then there are $N \in \mathbb{N}$ and an environment $e$ with
--   $$ \mathsf{step}^{N}(c) = \langle \mathsf{ret}\,r,\; e,\; [\,]\rangle , $$
--   that is, the machine run from $c$ reaches a final configuration, and its value is the result $r$ of the loop.
--
--   This is the backward half of the efficient universal machine (blueprint `lem:universal-tm`): if the universal program halts on $(\lceil p\rceil, v)$ with result $r$, then the machine run of $p$ on $v$ reaches a final configuration with value $r$, and by the correspondence between machine runs and derivations (`halts_iff`) the program $p$ halts on $v$ with result $r$. Without it, the universal program could halt with a value the simulated program never produces.
--
--   **Formalization Note**: The lemma is stated for an arbitrary configuration $c$ and arbitrary trailing environment $\rho$, and for any cost $t$, since it is proved by strong induction on $t$; no bound on $t$ or on sizes is needed. The number of machine steps $N$ is not related to $t$ in the statement.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Universal.lean#L185-L214; internal lemma of the formalization of blueprint lem:universal-tm, https://vidick.github.io/MIPRE-formalization/blueprint/

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

theorem MIPRE.Cost.Machine.interpLoop_rev : ∀ (t : ℕ) (c : Cfg) (env : Env) (r : Data),
    Eval (c.toData :: env) (.loop interpBody) r t → ∃ N e, step^[N] c = ⟨.ret r, e, []⟩ := by sorry
