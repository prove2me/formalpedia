-- Prove2me | Theorems.Thm_MIPRE_Verifier_sum_filter_length
-- name    : MIPRE.Verifier.sum_filter_length
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:39:13.782982+00:00
-- url     : https://prove2.me/theorems/dfd6a479-cf1e-4272-b0cf-593ce794c61b
-- title:
--   Counting a list of bit strings by the index pair each entry lands on: the double sum of the filter lengths is the length of the list
-- statement:
--   Let $N \in \mathbb N$, let $f_A, f_B : \{0,1\}^* \to \mathbb N$ be two indexing functions on bit strings, and let $l$ be a list of bit strings (with repetitions allowed) such that $f_A(z) < N$ and $f_B(z) < N$ for every entry $z$ of $l$. For $x, y \in \mathrm{Fin}\ N$ write $l|_{x, y}$ for the sublist of the entries $z$ of $l$ with $f_A(z) = x$ and $f_B(z) = y$ (`l.filter`). Then
--
--   $$ \sum_{x \in \mathrm{Fin}\, N}\ \sum_{y \in \mathrm{Fin}\, N}\ \bigl|\, l|_{x, y} \,\bigr| \;=\; |l| . $$
--
--   Every entry of $l$ is counted exactly once, at the index pair $(f_A(z), f_B(z))$, because that pair is in range. In the tabulation of a verifier's game, $l$ is the enumeration of the points of $\mathbb F_2^{s}$ as bit strings of length $s$ and $f_A, f_B$ the (tagged) indices of the two players' marginal questions, so the lemma gives the total weight $2^s$ of the weight list (`Verifier.totalWeight_weightList`), the denominator of the CL distribution of the sampler; `mu_clauseL` imports it to identify the tabulated distribution with the verifier's.
--
--   **Formalization Note**. The theorem is `MIPRE.Verifier.sum_filter_length {N : ℕ} (fA fB : BitStr → ℕ) (l : List BitStr) (hA : ∀ z ∈ l, fA z < N) (hB : ∀ z ∈ l, fB z < N)`, with conclusion `∑ x : Fin N, ∑ y : Fin N, (l.filter fun z => decide (fA z = x.val ∧ fB z = y.val)).length = l.length`, an equation in $\mathbb N$ over `Finset.univ` of `Fin N`. The filter predicate is the Boolean `decide` of the conjunction of two equalities of natural numbers; `BitStr` is `List Bool`, but nothing about bit strings is used beyond the type of the entries.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Tabulate.lean#L245-L278; internal lemma of the formalization of blueprint rem:compression-abstract (obligation O2, the weight list of the tabulated game)

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
open MIPRE.Verifier
open MIPRE.Cost
open HaltingGameValue (GameData)

theorem MIPRE.Verifier.sum_filter_length {N : ℕ} (fA fB : BitStr → ℕ) (l : List BitStr)
    (hA : ∀ z ∈ l, fA z < N) (hB : ∀ z ∈ l, fB z < N) :
    ∑ x : Fin N, ∑ y : Fin N,
      (l.filter fun z => decide (fA z = x.val ∧ fB z = y.val)).length = l.length := by sorry
