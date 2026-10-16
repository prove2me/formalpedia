-- Prove2me | Theorems.Thm_MIPRE_Halting_accepts_iff
-- name    : MIPRE.Halting.accepts_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:37:38.238804+00:00
-- url     : https://prove2.me/theorems/426193fe-97cc-4098-99e6-0e7fb948c535
-- title:
--   Acceptance of the halting verifier $\mathcal V^{\mathrm{halt}}$, branch by branch (blueprint `lem:dhalt-values`)
-- statement:
--   Fix a gap-preserving compression $G$ (`GapCompression`), with compressed sampler $\mathcal S^{\mathrm{compr}}_\lambda$ = `G.sampler lam` of dimension $s_\lambda(n)$ at index $n$ and output map `G.output`; an efficient universal machine $U$; a clocked universal machine $UT$; a search program $S'$; a machine $M$ and $\lambda \in \mathbb N$. The halting verifier $\mathcal V^{\mathrm{halt}}$ = `Vhalt G U UT S' M lam` is `Verifier.ofSamplerDecider U (G.sampler lam) (dec G U UT S' M lam)`: the compressed sampler at $\lambda$ with the self-referential decider $\mathcal D^{\mathrm{halt}}$, wrapped in the question-length check. A decider accepts $(n, x, y, a, b)$ when its program halts on $\mathrm{encode}(n, x, y, a, b)$ with output $\mathrm{encode}(\mathtt{true})$; a program halts within $k$ when it has a run on the empty input $\mathtt{nil}$ of cost at most $k$; $\mathrm{size}(n)$ is the binary length of $n$; `searchP S' lam d` is the program that, on the empty input, runs $S'$ on the encoding of the description string `descOf lam d` of $(\lambda, d)$.
--
--   For every $n \in \mathbb N$ and all bit strings $x, y, a, b$:
--
--   $$ \mathcal V^{\mathrm{halt}}\!.\mathrm{decider}\ \text{accepts}\ (n, x, y, a, b) \iff |x| = s_\lambda(n) \wedge |y| = s_\lambda(n) \wedge \begin{cases} \mathrm{True} & \text{if } M \text{ halts within } \mathrm{size}(n), \\ \mathrm{False} & \text{else, if } \mathrm{searchP}(S', \lambda, \mathcal D^{\mathrm{halt}}) \text{ halts within } \mathrm{size}(n), \\ \mathcal V^{\mathrm{compr}}\!.\mathrm{decider}\ \text{accepts}\ (n, x, y, a, b) & \text{otherwise}, \end{cases} $$
--
--   where $\mathcal V^{\mathrm{compr}}$ = `G.output ((Vhalt …).sampler.prog, (Vhalt …).decider.prog) lam` is the compressed verifier of $\mathcal V^{\mathrm{halt}}$ itself. This is the acceptance statement of blueprint `lem:dhalt-values`, from which the values at level $C$ are read off level by level.
--
--   **Formalization Note**. The theorem is `MIPRE.Halting.accepts_iff`, with $G$, $U$, $UT$ explicit. The case distinction is a nested `if … then True else if … then False else …` on the Booleans `(evalWithin M .nil (Nat.size n)).isSome` and `(evalWithin (searchP S' lam (dec G U UT S' M lam)) .nil (Nat.size n)).isSome`; `(evalWithin c v k).isSome` holds when some run of $c$ on $v$ has cost at most $k$, and `Nat.size` is Mathlib's binary length. `searchP S' lam d = hardcode (Prog.onLeft S') (encode (descOf lam d))`. No hypothesis on $S'$, $M$, $\lambda$ or $n$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/Decider.lean#L244-L271; blueprint lem:dhalt-values; the paper's `recursive.tex`, figure `fig:halt_f` (the decider of the halting verifier); [Lin25] J. Lin, MIP^co = coRE, Proc. 58th STOC, 2026, arXiv:2510.07162 (the search branch of the decider is Lin's)

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

theorem MIPRE.Halting.accepts_iff (S' M : Prog) (lam n : ℕ) (x y a b : BitStr) :
    (Vhalt G U UT S' M lam).decider.Accepts n x y a b ↔
      x.length = (G.sampler lam).dim n ∧ y.length = (G.sampler lam).dim n ∧
        (if (evalWithin M .nil (Nat.size n)).isSome then True
         else if (evalWithin (searchP S' lam (dec G U UT S' M lam)) .nil (Nat.size n)).isSome
           then False
         else (G.output ((Vhalt G U UT S' M lam).sampler.prog,
           (Vhalt G U UT S' M lam).decider.prog) lam).decider.Accepts n x y a b) := by sorry
