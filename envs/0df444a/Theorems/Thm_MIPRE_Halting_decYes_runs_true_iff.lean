-- Prove2me | Theorems.Thm_MIPRE_Halting_decYes_runs_true_iff
-- name    : MIPRE.Halting.decYes_runs_true_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:39:07.450474+00:00
-- url     : https://prove2.me/theorems/71600fe2-ae67-4f0b-a9f9-53ecddf130f6
-- title:
--   What the fixed-answer decider `decYes` accepts: the empty answer from both players, on every question pair
-- statement:
--   Ambient cost model: binary-tree data (`Data`), programs (`Prog`), the size-faithful encoding $\mathrm{encode}$ (a tuple $(n, x, y, a, b)$ of a number and four bit strings encodes as the right-nested chain $\mathtt{cons}(\mathrm{encode}\ n, \mathtt{cons}(\mathrm{encode}\ x, \mathtt{cons}(\mathrm{encode}\ y, \mathtt{cons}(\mathrm{encode}\ a, \mathrm{encode}\ b))))$, and the empty bit string encodes as $\mathtt{nil}$), and $p(v) \Downarrow_t r$ (`p.Runs v r t`) for a run of $p$ on the single input $v$ halting with result $r$ at cost $t$. A decider of a normal form verifier is a program whose input is $\mathrm{encode}(n, x, y, a, b)$, an index and the questions and answers of the two players, and which accepts when it halts with output $\mathrm{encode}(\mathtt{true})$. The fixed-answer decider `decYes` (`decYes_halts`) is the program of six nested $\mathtt{elim}$s that takes the tuple apart and tests the two answers.
--
--   For every $n \in \mathbb N$ and all bit strings $x, y, a, b$:
--
--   $$ \bigl(\exists\, t,\ \mathrm{decYes}(\mathrm{encode}(n, x, y, a, b)) \Downarrow_t \mathrm{encode}(\mathtt{true})\bigr) \iff a = [\,] \;\wedge\; b = [\,]. $$
--
--   So, once wrapped in the question-length check, the decider of the string $y_{\mathrm{yes}}$ accepts exactly the empty answer from both players, on every question pair, and nothing else. The module docstring records why this is the right decider for the accepting side of obligation O1: the paper's halting case accepts everything, which in the synchronous framework is not synchronous (equal questions with unequal answers must be rejected), whereas a fixed accepted answer gives a value-1 PCC strategy (`Verifier.hasPerfectPCC_of_accepts_diagonal`) and makes every long answer rejected (`yYes_mem`).
--
--   **Formalization Note**. The theorem is `MIPRE.Halting.decYes_runs_true_iff (n : ℕ) (x y a b : BitStr)`, with conclusion `(∃ t, decYes.Runs (encode (n, x, y, a, b)) (encode true) t) ↔ (a = [] ∧ b = [])`. The left-hand side is `Decider.Accepts` unfolded for the bare program `decYes` (the verifier's decider adds the question-length check); `encode true` is the datum $\mathtt{cons}(\mathtt{nil}, \mathtt{nil})$ and the empty bit string encodes as $\mathtt{nil}$, so the test the program performs is whether the fourth and fifth components of the input are $\mathtt{nil}$. The questions $x, y$ and the index $n$ are unconstrained.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Strings.lean#L105-L125; internal lemma of the formalization of blueprint thm:halting (obligation O1 of the halting reduction, the two distinguished strings)

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Halting
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
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings

open MIPRE
open MIPRE.Halting
open MIPRE.Cost

theorem MIPRE.Halting.decYes_runs_true_iff (n : ℕ) (x y a b : BitStr) :
    (∃ t, decYes.Runs (encode (n, x, y, a, b)) (encode true) t) ↔ (a = [] ∧ b = []) := by sorry
