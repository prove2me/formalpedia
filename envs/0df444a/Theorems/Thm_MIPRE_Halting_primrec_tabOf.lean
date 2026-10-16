-- Prove2me | Theorems.Thm_MIPRE_Halting_primrec_tabOf
-- name    : MIPRE.Halting.primrec_tabOf
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:39:21.465401+00:00
-- url     : https://prove2.me/theorems/7abab611-ecbf-4d71-a3cd-006a7cbbe921
-- title:
--   The doubled, re-budgeted tabulation of a verifier is primitive recursive in its parameters
-- statement:
--   `MIPRE.Halting.tabOf sd pd s T B k n` is the game description (`GameData`) tabulating at index $n$ the game of the normal form verifier with encoded sampler `sd` and encoded decider `pd`, question dimension $s$, answers of length at most $T$, and sampler budget $B\,(|q|+1)^k$ on a query of size $|q|$. Its fields are $nX = 2^{s+1} - 1$, $nA = |\mathtt{bitStrsLE}\ T| - 1$, the weight list with one entry of weight $1$ per point $z \in \mathbb{F}_2^s$ at the index pair $(\mathtt{bitsToIdx}(\mathtt{false} :: m_A(z)),\ \mathtt{bitsToIdx}(\mathtt{true} :: m_B(z)))$, where $m_w(z) = \mathtt{margOf}\ sd\ B\ k\ n\ w\ z$ is player $w$'s marginal question at $z$, and the acceptance list `accListW s T` at the tagged indexings $u \mapsto \mathtt{bitsToIdx}(\mathtt{false} :: u)$, $v \mapsto \mathtt{bitsToIdx}(\mathtt{true} :: v)$ with acceptance predicate `accOf pd n`. Let $\alpha$ be a `Primcodable` type, $k$ a fixed natural number, and $sd, pd : \alpha \to \mathtt{Data}$, $s, T, B, lvl : \alpha \to \mathbb{N}$ primitive recursive. Then
--
--   $$ a \;\longmapsto\; \mathtt{tabOf}\ (sd\ a)\ (pd\ a)\ (s\ a)\ (T\ a)\ (B\ a)\ k\ (lvl\ a) $$
--
--   is a primitive recursive function from $\alpha$ to `GameData`.
--
--   This is the computability half of obligation **O2** of blueprint `rem:compression-abstract`: the tabulation run by the instantiation of the compressibility criterion is computable, though not polynomial-time, from two encoded programs and five numbers; the bridge back to the verifier is in `Halting/Instantiation.lean`.
--
--   **Formalization Note** `GameData` is `Primcodable` through `GameData.equivTuple`. `tabOf` is plain data and not a `Verifier`, which carries proofs and cannot appear in a `Primrec` statement. The alphabet is doubled, Alice's index being her marginal's bit string with a `false` bit prepended and Bob's with a `true` bit, so $nX = 2^{s+1} - 1$; `bitsToIdx` reads a bit string as a binary number, least significant bit first. `margOf sd B k n w z` is `Machine.runForD sd (encode (n, Query.marginal w 7 z)) (B * (|encode (Query.marginal w 7 z)| + 1) ^ k)` decoded to a bit string, with default `[]` when the run does not finish or does not decode. `accOf pd n` runs the decider at the budget $n^n$ of $n$-boundedness, not at $B, k$. The degree `k` is a fixed natural number, not a function of `a`. Hypotheses: `[Primcodable α]` and `Primrec` for each of `sd pd s T B lvl`. Namespace `MIPRE.Halting`, module `MIPRE.Foundations.Halting.Tabulate`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Tabulate.lean#L732-L753

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

theorem MIPRE.Halting.primrec_tabOf {α : Type*} [Primcodable α] {sd pd : α → Data} {s T B lvl : α → ℕ}
    (k : ℕ) (hsd : Primrec sd) (hpd : Primrec pd) (hs : Primrec s) (hT : Primrec T)
    (hB : Primrec B) (hlvl : Primrec lvl) :
    Primrec fun a : α => tabOf (sd a) (pd a) (s a) (T a) (B a) k (lvl a) := by sorry
