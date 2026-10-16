-- Prove2me | Theorems.Thm_MIPRE_Halting_body_runs_iff
-- name    : MIPRE.Halting.body_runs_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:37:27.502347+00:00
-- url     : https://prove2.me/theorems/aa7a5e7c-b6b9-44ec-bf9b-357a80a1055d
-- title:
--   The body of the halting decider: a run of `body` is a run of the program `prep` selects on the input it selects
-- statement:
--   Ambient cost model of the formalization: programs (`Prog`) run on binary-tree data (`Data`); $\mathrm{encode}$ is the size-faithful encoding of numbers, bit strings, programs and tuples as data (a tuple is a right-nested chain of $\mathtt{cons}$ cells; a datum encodes as itself); $p(v) \Downarrow_t r$ (`p.Runs v r t`) means that $p$ run on the single input $v$ halts with result $r$ at cost $t$. Fix a gap-preserving compression $G$ (`GapCompression`), an efficient universal machine $U$, a clocked universal machine $UT$, and a program $S'$ (the search program).
--
--   The paper-route decider of the halting verifier is built from the polynomial-time function `prep G U UT S'`: on a description $(M, (\lambda, d'))$ and an input $(n, \mathit{rest})$ it returns the pair (program to run, its input) selected by the three branches of the decider: the constant-$\mathtt{true}$ program if $M$ halts on the empty input within cost $\mathrm{size}(n)$ (the binary length of $n$), else the constant-$\mathtt{false}$ program if the search program of $(\lambda, d')$ does, else the compressed decider of $(\mathcal S^{\mathrm{compr}}_\lambda, \mathrm{wrap}\ d')$ on $\mathrm{encode}(n, \mathit{rest})$. The body `body G U UT S'` runs the program of `prep` on its input, then calls the universal machine on the pair returned.
--
--   Let $P \in \mathrm{Prog} \times (\mathbb N \times \mathrm{Prog})$, $n \in \mathbb N$ and $\mathit{rest}, r \in \mathrm{Data}$. Then
--
--   $$ \bigl(\exists t,\ \mathrm{body}(\mathrm{encode}(P,(n,\mathit{rest}))) \Downarrow_t r\bigr) \iff \bigl(\exists t,\ \pi_1(\mathrm{prep}(P,(n,\mathit{rest})))\bigl(\pi_2(\mathrm{prep}(P,(n,\mathit{rest})))\bigr) \Downarrow_t r\bigr). $$
--
--   Costs on the two sides are not related. With `dec_runs_iff`, this reduces the acceptance of the halting verifier (`accepts_iff`, blueprint `lem:dhalt-values`) to running `prep` and reading its output.
--
--   **Formalization Note**. The theorem is `MIPRE.Halting.body_runs_iff`, with $G$, $U$, $UT$ explicit. `body G U UT S'` is `.let_ (prep G U UT S').code (callVar 0 U.univ)`, with `callVar 0 q = .let_ (.var 0) q`; `prep` is a `PolyTimeFun` applied through its coercion to a function, and `.1`, `.2` project the pair it returns. $P$ is any element of $\mathrm{Prog} \times (\mathbb N \times \mathrm{Prog})$, not only a description $(M, (\lambda, \mathrm{dec}))$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/Decider.lean#L203-L226; blueprint lem:halt-construction; the paper's `recursive.tex`, figure `fig:halt_f` (the decider of the halting verifier); [Lin25] J. Lin, MIP^co = coRE, Proc. 58th STOC, 2026, arXiv:2510.07162 (the search branch of the decider is Lin's)

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
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_ManyOne
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Definitions.Def_MIPRE_Foundations_Halting_Reduction
import Definitions.Def_MIPRE_Foundations_Halting_Compressor
import Definitions.Def_MIPRE_Foundations_Halting_Paper_TabulateL
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Decider

open MIPRE
open MIPRE.Halting
open MIPRE.Cost MIPRE.Cost.Prog MIPRE.Cost.Prog.ProgD Polynomial
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)

theorem MIPRE.Halting.body_runs_iff (S' : Prog) (P : Prog × (ℕ × Prog)) (n : ℕ) (rest r : Data) :
    (∃ t, (body G U UT S').Runs (encode (P, (n, rest))) r t) ↔
      ∃ t, (prep G U UT S' (P, (n, rest))).1.Runs (prep G U UT S' (P, (n, rest))).2 r t := by sorry
