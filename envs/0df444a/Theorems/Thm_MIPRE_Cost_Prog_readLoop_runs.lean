-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_readLoop_runs
-- name    : MIPRE.Cost.Prog.readLoop_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:27:16.801189+00:00
-- url     : https://prove2.me/theorems/6f149afc-00ce-4c68-a07e-3cbe7d071126
-- title:
--   The compressor's reading loop reads the described string from a succinct description
-- statement:
--   Let $U$ be an efficient universal machine (`UniversalMachine`): a closed program `U.univ` with an overhead polynomial `U.bound`, such that a run of a program $c$ on $v$ with result $r$ at cost $t$ gives a run of `U.univ` on `cons (encode c) v` with result $r$ within cost `U.bound.eval (esize c + v.size + t)`, and `U.univ` halts on `cons (encode c) v` only if $c$ halts on $v$ with the same result. `IsSuccinctDesc c n x` says that $(c, n)$ succinctly describes the bit string $x$: $c$ is closed, $|x| \le 2^n$, and for every $m$, $c$ on `encode m` halts with `bitQueryAnswer x m` within cost $(n + 1)(\mathrm{size}\ m + 1)^2$, where `bitQueryAnswer x m` is `encode` of the $m$-th bit of $x$ for $m < |x|$ and the marker `ofNat 2` otherwise. The reading loop iterates `readBody U.univ` — one bit query through the universal machine per iteration — on the state `readState cD x i = cons cD (cons (encode i) (encode (x.take i).reverse))`. `readIter U s n L` is the explicit per-iteration cost for a description of size $s$ at parameter $n$ and a string of length at most $L$: the overhead polynomial evaluated at $s + (4\,\mathrm{size}\ L + 1) + (n + 1)(\mathrm{size}\ L + 1)^2$, plus the bookkeeping terms $3s + 4(4\,\mathrm{size}\ L + 1) + (4L + 1) + 2(\mathrm{size}\ L + 2)(8(4\,\mathrm{size}\ L + 1) + 8\,\mathrm{size}\ L + 60) + 30$. Let `env` be any environment. Then
--
--   $$\exists\, t \le (|x| + 1)\big(\mathrm{readIter}\ U\ (\mathrm{esize}\ c)\ n\ |x| + 1\big),\qquad \mathrm{Eval}\ \big(\mathrm{readState}\ (\mathrm{encode}\ c)\ x\ 0 :: env\big)\ \big(\mathrm{loop}\ (\mathrm{readBody}\ U.\mathrm{univ})\big)\ \big(\mathrm{encode}\ (\mathrm{reverse}\ x)\big)\ t .$$
--
--   This is the loop of `readProg`, the first stage of the compressor's decider: the string to be compressed is recovered from its succinct description by bit queries instead of being hardcoded as in the paper's machine 𝓕.
--
--   **Formalization Note** The initial state `readState (encode c) x 0` is `cons (encode c) (cons nil nil)`, since `encode 0` and `encode []` are both `nil`; the result is the encoding of the reversed string, which `readProg` reverses afterwards. `readIter` is noncomputable only through the evaluation of `U.bound`; `size` is `Nat.size` and `esize c = (encode c).size`. `c`, `n`, `x` are implicit, determined by `hsd`; `U` and `env` are explicit. The proposition is `MIPRE.Cost.Prog.readLoop_runs`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Compressor.lean#L190-L264; paper recursive.tex, fig:halt_f (the compressor's decider is the paper's machine 𝓕 with the recursion removed)

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.UnitaryGroup
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
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec
import Definitions.Def_MIPRE_Foundations_ValueApprox_RE
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
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
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
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Definitions.Def_MIPRE_Foundations_Halting_Reduction
import Definitions.Def_MIPRE_Foundations_Halting_Compressor

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.readLoop_runs (U : UniversalMachine) {c : Prog} {n : ℕ} {x : BitStr}
    (hsd : IsSuccinctDesc c n x) (env : Env) :
    ∃ t ≤ (x.length + 1) * (readIter U (esize c) n x.length + 1),
      Eval (readState (encode c) x 0 :: env) (.loop (readBody U.univ)) (encode x.reverse) t := by sorry
