-- Prove2me | Theorems.Thm_MIPRE_Halting_valStar_le_of_not_halts
-- name    : MIPRE.Halting.valStar_le_of_not_halts
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:37:26.54162+00:00
-- url     : https://prove2.me/theorems/a7cce046-d170-4c66-b71b-5eaac52da2f0
-- title:
--   The non-halting case: if $M$ does not halt, the halting verifier has quantum value at most $1/2$ at level $C$
-- statement:
--   Setting of the paper-route halting reduction: a gap-preserving compression $G$ with constant $C_0$ and bounding polynomial $\mathrm{bound}$; an efficient universal machine $U$; a clocked universal machine $UT$; a search program $S'$; a machine $M$ (a program) and $\lambda \in \mathbb N$; $C := \max(C_0, 2)$; $\mathcal V^{\mathrm{halt}}$ = `Vhalt G U UT S' M lam` the halting verifier (`accepts_iff`). $\mathrm{val}^*(\mathcal V_n, T)$ = `V.valStar n T` is the quantum (tensor-product) value of the $n$-th game of a verifier with answers of length at most $T$; for a bit string $x$, `tabL G U x n` is the game description tabulating the $n$-th game of the verifier `Vof G U x` the string denotes, and `quantumValue (tabL G U x n).game` the quantum value of the described game. Hypotheses: (hS') $S'$ is closed (`S'.WellScoped 1`); (hsem) for every bit string $x$, $S'$ halts on $\mathrm{encode}(x)$ if and only if $\tfrac12 < \mathrm{val}^*(\mathrm{tabL}(x, C))$; (hb) $\mathcal V^{\mathrm{halt}}$ is $\lambda$-bounded (`IsBounded lam`: for every $n \ge 2$ the sampler's dimension is at most $n^\lambda$, the sampler and the decider halt within cost $n^\lambda(|d|+1)^\lambda$ on every input $(n, d)$, and the description length is at most $\lambda$); (hpoly) $\mathrm{bound}(n + \lambda) \le n^\lambda$ for all $n \ge 2$; (hM) $M$ does not halt on the empty input. Then
--
--   $$ \mathrm{val}^*\bigl(\mathcal V^{\mathrm{halt}}_{C},\ \mathrm{bound}(C + \lambda)\bigr) \;\le\; \tfrac12 . $$
--
--   This is item 2 of blueprint `thm:halting` in the paper's form, at the fixed level $C$ and with the answer alphabet cut at $\mathrm{bound}(C + \lambda)$, the length beyond which the compressed decider rejects. The halting case is `hasPerfectPCC_of_halts`; `Paper/Main.lean` discharges the four standing hypotheses with the search program `semL` and the threshold of `lem:lambda`, and combines the two into `halting_paper`.
--
--   **Formalization Note**. The theorem is `MIPRE.Halting.valStar_le_of_not_halts`; its signature, in order, is $G$, $U$, $UT$ (explicit), $S'$ (implicit), `hS'`, `hsem`, $M$, $\lambda$, `hb`, `hpoly`, `hM : ¬ Halts M .nil`, with conclusion `(Vhalt G U UT S' M lam).valStar (C G) (G.bound.eval (C G + lam)) ≤ 1 / 2` in $\mathbb R$. `valStar n T = quantumValue (V.game n T)`, the supremum of the values of tensor-product strategies; `C G = max G.C₀ 2`; `hsem` is stated with `(1 : ℝ) / 2` and `quantumValue (tabL G U x (C G)).game`; `Halts M .nil` is `∃ r t, Eval [.nil] M r t`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/Induction.lean#L326-L349; blueprint thm:halting

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
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Induction

open MIPRE
open MIPRE.Halting
open MIPRE.Cost MIPRE.Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable {S' : Prog} (hS' : S'.WellScoped 1)
  (hsem : ∀ x : BitStr, Halts S' (encode x) ↔
    (1 : ℝ) / 2 < quantumValue (tabL G U x (C G)).game)
  (M : Prog) (lam : ℕ)
  (hb : (Vhalt G U UT S' M lam).IsBounded lam)
  (hpoly : ∀ n, 2 ≤ n → G.bound.eval (n + lam) ≤ n ^ lam)
include hS' hsem hb hpoly

theorem MIPRE.Halting.valStar_le_of_not_halts (hM : ¬ Halts M .nil) :
    (Vhalt G U UT S' M lam).valStar (C G) (G.bound.eval (C G + lam)) ≤ 1 / 2 := by sorry
