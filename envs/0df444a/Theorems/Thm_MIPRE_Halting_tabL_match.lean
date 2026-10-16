-- Prove2me | Theorems.Thm_MIPRE_Halting_tabL_match
-- name    : MIPRE.Halting.tabL_match
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-15T19:38:35.997336+00:00
-- url     : https://prove2.me/theorems/b786fd0b-6ae3-4295-a1b7-d75f26077cab
-- title:
--   The tabulation `tabL` matches the doubled game of the verifier the string denotes, up to relabelings of questions and answers
-- statement:
--   Fix a gap-preserving compression $G$ and an efficient universal machine $U$. A bit string $x$ denotes the verifier $\mathcal V_x$ = `Vof G U x`: the compressed sampler at the string's own parameter $\lambda_x$ = `descLam x`, with the decider datum the string carries, wrapped in the question-length check. Its $n$-th game has questions $\mathbb F_2^{s(n)}$ and, with the answer cut $T$ = `ansBound G x n` = $\mathrm{bound}(n + \lambda_x)$, answers $\mathrm{Answers}(T)$, the bit strings of length at most $T$. The doubled game $\mathcal V_x^{\mathrm{dbl}}$ = `(Vof G U x).doubledGame n T` plays on $\mathrm{Bool} \times \mathbb F_2^{s(n)}$: Alice's questions are tagged $\mathtt{false}$ and Bob's $\mathtt{true}$; a pair of an Alice question and a Bob question has the sampler's probability and the decider's verdict, every other pair of tags weight $0$ and rejection. The tabulation `tabL G U x n` is the `GameData` describing that game with the decider budgeted from $\lambda_x$, and `(tabL G U x n).game` the two-player game it describes, on questions $\mathrm{Fin}(n_X + 1)$ and answers $\mathrm{Fin}(n_A + 1)$, with distribution $\mu$ and Boolean decision predicate $D$.
--
--   Assume (hb) `(Vof G U x).IsBounded (descLam x)`, that the verifier the string denotes is bounded by the string's own parameter, and (hn) $2 \le n$. Then
--
--   $$ \exists\, e_X : \mathrm{Fin}(n_X + 1) \simeq \mathrm{Bool} \times \mathbb F_2^{s(n)},\ \exists\, e_A : \mathrm{Fin}(n_A + 1) \simeq \mathrm{Answers}(T):\quad \bigl(\forall i\, j,\ \mu_{\mathrm{tabL}}(i, j) = \mu_{\mathcal V_x^{\mathrm{dbl}}}(e_X i, e_X j)\bigr) \wedge \bigl(\forall i\, j\, k\, l,\ D_{\mathrm{tabL}}(i, j, k, l) = D_{\mathcal V_x^{\mathrm{dbl}}}(e_X i, e_X j, e_A k, e_A l)\bigr). $$
--
--   So the tabulated game is the doubled game of $\mathcal V_x$ up to a bijective relabeling of each alphabet, on every string whose verifier is bounded by its own parameter, at every level $n \ge 2$. It is the input to the value agreement `tabL_value` (the quantum value of the tabulation equals $\mathrm{val}^*(\mathcal V_x, n, T)$), on which the semidecider of the search branch rests.
--
--   **Formalization Note**. The theorem is `MIPRE.Halting.tabL_match`, with $G$, $U$ explicit and hypotheses `hb : (Vof G U x).IsBounded (descLam x)`, `hn : 2 ≤ n`. The $\mu$ clause is an equality of real numbers and the $D$ clause one of Booleans, `game.D` of a `GameData` rejecting unequal answers at equal questions whatever its table holds.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/TabulateL.lean#L344-L371; internal lemma of the tabulation of the halting reduction along the paper's route (the game the search branch of the paper-route decider tests)

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
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Paper_TabulateL

open MIPRE
open MIPRE.Halting
open MIPRE.Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)

theorem MIPRE.Halting.tabL_match (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded (descLam x)) (hn : 2 ≤ n) :
    ∃ (eX : Fin ((tabL G U x n).nX + 1) ≃ Bool × (Vof G U x).Questions n)
      (eA : Fin ((tabL G U x n).nA + 1) ≃ Verifier.Answers (ansBound G x n)),
      (∀ i j, (tabL G U x n).game.μ i j
        = ((Vof G U x).doubledGame n (ansBound G x n)).μ (eX i) (eX j)) ∧
      (∀ i j k l, (tabL G U x n).game.D i j k l
        = ((Vof G U x).doubledGame n (ansBound G x n)).D (eX i) (eX j) (eA k) (eA l)) := by sorry
