-- Prove2me | Theorems.Thm_MIPRE_Halting_decYes_halts
-- name    : MIPRE.Halting.decYes_halts
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:38:40.728886+00:00
-- url     : https://prove2.me/theorems/8fabe114-7554-4c0c-b587-5b4346b5e4bf
-- title:
--   The fixed-answer decider `decYes` halts on every input at cost at most 10
-- statement:
--   Ambient cost model: data are binary trees (`Data`), programs (`Prog`) are built from variables, $\mathtt{nil}$, literals, $\mathtt{cons}$, the case analysis $\mathtt{elim}\ i\ n\ c$ (run $n$ if variable $i$ holds $\mathtt{nil}$, else run $c$ with the two components of the $\mathtt{cons}$ bound as new variables), $\mathtt{let}$ and $\mathtt{loop}$, and $p(v) \Downarrow_t r$ (`p.Runs v r t`) means that $p$ on the single input $v$ halts with result $r$ at cost $t$, one unit per evaluation rule plus the size of every value read or built. The fixed-answer decider `decYes` is the program of six nested $\mathtt{elim}$s, with no loop and no variable read, which on a well-formed tuple $(n, x, y, a, b)$ takes the tuple apart and returns $\mathrm{encode}(\mathtt{true})$ exactly when both answers $a$ and $b$ are the empty bit string (`decYes_runs_true_iff`), and returns $\mathtt{nil}$ otherwise. It is the decider of the distinguished string $y_{\mathrm{yes}}$ of obligation O1 of the halting reduction.
--
--   $$ \forall v \in \mathrm{Data},\ \exists\, r\ t,\qquad t \le 10 \;\wedge\; \mathrm{decYes}(v) \Downarrow_t r . $$
--
--   So `decYes` is total, on inputs well formed or not, at a constant cost. This is what the $\lambda$-boundedness of the verifier $y_{\mathrm{yes}}$ denotes needs of its decider (`Verifier.ofSamplerDecider_isBounded` asks for a polynomially bounded cost, `decYes_hasPolyCost`), the sampler's bounds being fields of `GapCompression`.
--
--   **Formalization Note**. The theorem is `MIPRE.Halting.decYes_halts (v : Data) : ∃ r t, t ≤ 10 ∧ decYes.Runs v r t`; the result $r$ is existentially quantified and not specified (it is $\mathrm{encode}(\mathtt{true})$ or $\mathtt{nil}$ according to the shape of $v$), and the bound $10$ is an upper bound on the cost in the timed semantics of `Eval`, in which each $\mathtt{elim}$ costs one unit plus the cost of its continuation. The docstring records the reason: each of the program's $\mathtt{elim}$s either returns $\mathtt{nil}$ at once or descends one node of the input.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Strings.lean#L84-L99; internal lemma of the formalization of blueprint thm:halting (obligation O1 of the halting reduction, the two distinguished strings)

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

theorem MIPRE.Halting.decYes_halts (v : Data) : ∃ r t, t ≤ 10 ∧ decYes.Runs v r t := by sorry
