-- Prove2me | Theorems.Thm_MIPRE_Halting_primrec_accOf
-- name    : MIPRE.Halting.primrec_accOf
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:39:29.549172+00:00
-- url     : https://prove2.me/theorems/33bc7a9d-4a7a-4e49-95d8-7c7765f0205a
-- title:
--   The budgeted acceptance test of a tabulated decider is primitive recursive
-- statement:
--   The data of the ambient cost model are binary trees (`Data`), in which numbers, bit strings, tuples and programs are encoded; `Machine.runForD pd x k` runs the datum `pd`, read as a program, on the datum `x` for a cost budget `k`, and returns `some r` if the run halts within the budget with result `r` and `none` otherwise (a total, computable function). For a datum `pd`, a level $n$ and bit strings $x, y, a, b$, the Boolean `accOf pd n x y a b` is `true` exactly when running `pd` on the encoding of $(n, x, y, a, b)$ under the budget
--
--   $$ \mathtt{acceptBudget}\ (n^n)\ n\ x\ y\ a\ b \;=\; n^n \cdot \bigl(|\mathrm{encode}(x, y, a, b)| + 1\bigr)^n $$
--
--   halts within the budget with output `encode true`. Let $\alpha$ be a `Primcodable` type and let $pd : \alpha \to \mathtt{Data}$ and $lvl : \alpha \to \mathbb{N}$ be primitive recursive. Then the function on quintuples $q = (q_1, x, y, a, b) \in \alpha \times \mathrm{BitStr}^4$ given by $q \mapsto \mathtt{accOf}\ (pd\ q_1)\ (lvl\ q_1)\ x\ y\ a\ b$ is primitive recursive.
--
--   This is the first half of obligation **O2** of blueprint `rem:compression-abstract`, the computability of the acceptance table of the tabulated game: acceptance by a decider is a $\Sigma_1$ statement, and `accOf` decides it from the encoded decider program alone, at the budget $n^n$ that $n$-boundedness supplies (`MIPRE.Halting.accOf_iff` relates it to `Decider.Accepts` under that bound). The statement is generic in the ambient parameter type $\alpha$ so that `primrec_tabOf` can use it at any tuple shape without recomposing it.
--
--   **Formalization Note** `accOf pd n x y a b := decide (Machine.runForD pd (encode (n, x, y, a, b)) (Decider.acceptBudget (n ^ n) n x y a b) = some (encode true))`, with `Decider.acceptBudget T k x y a b := T * ((encode (x, y, a, b) : Data).size + 1) ^ k` and `Data.size` the number of nodes of a datum; `runForD` iterates the step function `3 k` times and reads off the result if the configuration reached is final. The decider is a datum `pd : Data`, not a `Prog`, so that `Primrec` can mention it; The argument is `q : α × BitStr × BitStr × BitStr × BitStr`, with `q.1 : α` and `q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2` the four strings. Hypotheses: `[Primcodable α]`, `hpd : Primrec pd`, `hlvl : Primrec lvl`. The source compiles it under `set_option maxHeartbeats 1000000`. Namespace `MIPRE.Halting`, module `MIPRE.Foundations.Halting.Tabulate`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Tabulate.lean#L689-L730

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate

open MIPRE
open MIPRE.Halting
open MIPRE.Cost
open HaltingGameValue (GameData)
set_option maxHeartbeats 1000000

theorem MIPRE.Halting.primrec_accOf {α : Type*} [Primcodable α] {pd : α → Data} {lvl : α → ℕ}
    (hpd : Primrec pd) (hlvl : Primrec lvl) :
    Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      accOf (pd q.1) (lvl q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 := by sorry
