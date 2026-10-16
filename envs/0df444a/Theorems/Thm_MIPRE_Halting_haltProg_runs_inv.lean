-- Prove2me | Theorems.Thm_MIPRE_Halting_haltProg_runs_inv
-- name    : MIPRE.Halting.haltProg_runs_inv
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:27:21.35344+00:00
-- url     : https://prove2.me/theorems/db56632d-bd88-4172-9388-40b9e81e02b4
-- title:
--   Inversion for the compressor's decider: it halts only if the universal machine halts on the compressed decider
-- statement:
--   Let $G$ be a gap-preserving compression and $U$ an efficient universal machine (a closed program `U.univ` with its overhead polynomial and simulation guarantees). The compressor's decider before hardcoding, `haltProg G U`, is the closed program that on an input `cons P d` — with $P$ = `encode (c, n, λ)` and $d$ the decider's own input — runs the preparation `prepProg G U` on $P$ to obtain the description of the compressed decider, pairs that description with $d$, and runs `U.univ` on the pair, returning its result. `compressedD G U x n λ` is the encoding of `G.compress` applied to the sampler and decider programs of the verifier $x$ denotes, frozen at index $2n + 1$, and to $\lambda$. `p.Runs x r t` is `Eval [x] p r t`. Assume `IsSuccinctDesc c n x` ($c$ is closed, $|x| \le 2^n$, and $c$ answers every bit query about $x$ within cost $(n + 1)(\mathrm{size}\ m + 1)^2$), let $\lambda$ be a natural number, $d$ and $r$ data and $t$ a cost, and assume `(haltProg G U).Runs (cons (encode (c, n, λ)) d) r t`. Then
--
--   $$\exists\, t',\qquad U.\mathrm{univ}.\mathrm{Runs}\ \big(\mathrm{cons}\ (\mathrm{compressedD}\ G\ U\ x\ n\ \lambda)\ d\big)\ r\ t' .$$
--
--   With the forward run `haltProg_runs` this gives `haltProg_accepts_iff`: the decider with $(c, n, \lambda)$ in front accepts exactly what the compressed decider of the frozen verifier of $x$ accepts; from it `comprStr_accepts`, the field `CompressorSpec.accepts_compr` of obligation O4 of blueprint `rem:compression-abstract`, follows (blueprint `lem:halt-construction`).
--
--   **Formalization Note** No cost bound is asserted on $t'$, and the result $r$ is the same datum on both sides. The input $d$ is arbitrary data, not required to be a well-formed `encode (m, x', y', a, b)`. The hypothesis `hsd : IsSuccinctDesc c n x` is part of the statement, and $x$ enters the conclusion only through `compressedD`. `c`, `x`, `n`, `d`, `r`, `t` are implicit, `lam` is explicit, `G` and `U` are section variables; the proposition is `MIPRE.Halting.haltProg_runs_inv`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Compressor.lean#L794-L814; blueprint lem:halt-construction; paper recursive.tex, fig:halt_f (the compressor's decider is the paper's machine 𝓕 with the recursion removed)

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
open MIPRE.Halting
open MIPRE.Cost
open MIPRE.Cost MIPRE.Cost.Prog MIPRE.Cost.Prog.ProgD
variable (G : GapCompression) (U : UniversalMachine)

theorem MIPRE.Halting.haltProg_runs_inv {c : Prog} {x : BitStr} {n : ℕ} (hsd : IsSuccinctDesc c n x) (lam : ℕ)
    {d r : Data} {t : ℕ} (h : (haltProg G U).Runs (.cons (encode (c, n, lam)) d) r t) :
    ∃ t', U.univ.Runs (.cons (compressedD G U x n lam) d) r t' := by sorry
