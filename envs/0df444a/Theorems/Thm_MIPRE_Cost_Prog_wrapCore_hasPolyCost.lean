-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_wrapCore_hasPolyCost
-- name    : MIPRE.Cost.Prog.wrapCore_hasPolyCost
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:39:37.776092+00:00
-- url     : https://prove2.me/theorems/011dda82-acb0-4edd-8486-2bd9bc8610e6
-- title:
--   The wrapper decider halts within a polynomially bounded cost on every input
-- statement:
--   Let $U$ be a universal machine of the ambient cost model, $S$ an $\ell$-level sampler and `dec` a program, the decider a string carries. The wrapper `wrapCore U.univ S.prog (encode dec)` is the program that, on an input $(N, x, y, a, b)$, runs `S.prog` on $(N, \mathtt{dimension})$ through `U.univ`, converts the dimension $s(N)$ to unary, compares it with the lengths of $x$ and of $y$ and, if both agree, runs `dec` on the whole input through `U.univ`, rejecting otherwise; it is how the compressibility criterion reads a string as a normal form verifier (blueprint `rem:compression-abstract`, item 1). A program $p$ *has polynomial cost* when there are $C : \mathbb{N} \to \mathbb{N}$ polynomially bounded and $k \in \mathbb{N}$ such that on every index $n$ and every datum $d$, well formed or not, $p$ halts on $(\mathrm{encode}\ n, d)$ within cost $C(n)(|d|+1)^k$. Theorem: if `S.prog` has polynomial cost, `S.dim` is polynomially bounded and `dec` has polynomial cost, then the wrapper has polynomial cost:
--
--   $$ \exists\, C\ k,\ \mathrm{PolyBounded}(C) \;\wedge\; \forall n\ d,\ \exists\, r\ t,\ t \le C(n)\,(|d|+1)^k \;\wedge\; \mathtt{wrapCore}\ U.\mathrm{univ}\ S.\mathrm{prog}\ (\mathrm{encode}\ dec)\ \text{ runs on } (\mathrm{encode}\ n,\ d) \text{ to } r \text{ in cost } t . $$
--
--   This is what inhabits `Verifier.IsBounded` for the verifier a string denotes (`Verifier.ofSamplerDecider_isBounded`), and so what makes the classes of descriptions `classA`, `classB` of the criterion inhabited at all. The bound is on arbitrary data because `Decider.TimeBoundAt` quantifies over every input at an index, not only over question pairs.
--
--   **Formalization Note** `Prog.HasPolyCost p := ∃ (C : ℕ → ℕ) (k : ℕ), PolyBounded C ∧ ∀ (n : ℕ) (d : Data), ∃ r t, t ≤ C n * (d.size + 1) ^ k ∧ p.Runs (.cons (encode n) d) r t`, where `Prog.Runs v r t` is the timed big-step semantics of the ambient model and `Data.size` the number of nodes. The decider enters as the datum `encode dec`, run through the universal machine. The three hypotheses are exactly `hS : S.prog.HasPolyCost`, `hdim : PolyBounded S.dim` and `hdec : dec.HasPolyCost`; for a sampler of a `GapCompression` all three come from its fields through `CL.Sampler.hasPolyCost_of_timeBound`. The section variables `U : UniversalMachine`, `S : CL.Sampler ℓ`, `dec : Prog` are explicit and `ℓ` is implicit. Namespace `MIPRE.Cost.Prog`, module `MIPRE.Foundations.Halting.WrapperCost`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/WrapperCost.lean#L455-L486

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
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
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.Data
variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ) (dec : Prog)

theorem MIPRE.Cost.Prog.wrapCore_hasPolyCost (hS : S.prog.HasPolyCost) (hdim : PolyBounded S.dim)
    (hdec : dec.HasPolyCost) : (wrapCore U.univ S.prog (encode dec)).HasPolyCost := by sorry
