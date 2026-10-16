-- Prove2me | Theorems.Thm_MIPRE_Verifier_length_filter_bitStrsOfLen
-- name    : MIPRE.Verifier.length_filter_bitStrsOfLen
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:39:15.237589+00:00
-- url     : https://prove2.me/theorems/7950d065-c190-4657-b16d-def2f9f5e278
-- title:
--   Counting over $\mathbb{F}_2^s$ by enumerating the bit strings of length $s$
-- statement:
--   Let $s$ be a natural number and write $\mathbb{F}_2$ for the field with two elements. `Data.bitStrsOfLen s` is the list of all bit strings (lists of Booleans) of length exactly $s$, enumerated without repetition, and for a bit string $z$ the vector `CL.ofBits s z` $\in \mathbb{F}_2^s$ has $i$-th coordinate $1$ when the $i$-th bit of $z$ is `true` and $0$ otherwise. Let $P : \mathbb{F}_2^s \to \mathrm{Bool}$ be an arbitrary Boolean predicate on vectors. Then the number of bit strings of length $s$ whose vector satisfies $P$ equals the number of vectors of $\mathbb{F}_2^s$ satisfying $P$:
--
--   $$ \bigl|\,\{\, z \in \mathtt{bitStrsOfLen}\ s \;:\; P(\mathtt{ofBits}\ s\ z) = \mathtt{true} \,\}\,\bigr| \;=\; \bigl|\,\{\, v \in \mathbb{F}_2^s \;:\; P(v) = \mathtt{true} \,\}\,\bigr| , $$
--
--   where the left side is the length of the filtered list and the right side the cardinality of the filtered finite set of all vectors.
--
--   In the tabulation of a normal form verifier as a game description (blueprint `rem:compression-abstract`), the weight list enumerates the bit strings of length $s(n)$, one entry of weight $1$ per point of $\mathbb{F}_2^{s(n)}$. This lemma is the bridge between that list and the vectors: it turns the tabulation's question weights into the numerator of the conditionally linear distribution `CL.clDist`, which counts vectors.
--
--   **Formalization Note** The left side is `((Data.bitStrsOfLen s).filter fun z => P (CL.ofBits s z)).length` and the right side is `(Finset.univ.filter fun v : Fin s → CL.𝔽₂ => P v = true).card`; since `P` is `Bool`-valued, the finset predicate is `P v = true`. `CL.𝔽₂` is `ZMod 2`, and a vector is a function `Fin s → 𝔽₂`. `CL.ofBits s l` is total on all bit strings, `fun i => if l.getD i false then 1 else 0`: missing bits read as `0` and bits beyond position `s` are ignored; on strings of length exactly `s` it is inverse to `CL.toBits`. `Data.bitStrsOfLen` is defined by recursion (`[[]]` at `0`; at `k + 1` every string of length `k` is extended by `false` and by `true`), and its members are exactly the strings of length `s`. The only arguments are `s` (implicit) and `P`. Namespace `MIPRE.Verifier`, module `MIPRE.Foundations.Halting.Tabulate`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Tabulate.lean#L294-L314

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

theorem MIPRE.Verifier.length_filter_bitStrsOfLen {s : ℕ} (P : (Fin s → CL.𝔽₂) → Bool) :
    ((Data.bitStrsOfLen s).filter fun z => P (CL.ofBits s z)).length
      = (Finset.univ.filter fun v : Fin s → CL.𝔽₂ => P v = true).card := by sorry
