-- Prove2me | Theorems.Thm_MIPRE_AnswerReduction_side_honest
-- name    : MIPRE.AnswerReduction.side_honest
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:59:34.928418+00:00
-- url     : https://prove2.me/theorems/2b72a0f9-4664-4065-8602-832fccf293ed
-- title:
--   Lemma side_honest of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Background.AnswerReduction.Honest` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Honest answers of the answer-reduced verifier. Piece AR-4 of `planning/answer-reduction.md`, the combinatorial half: the decision predicate `accepts` of `fig:decider-pcp` accepts the honest answers of two players who answer from polynomial data that is consistent in the ways the five steps check. A player's data (`HPolys`) is five `m`-variate polynomials `g₁ … g₅`, one for each of the first five copies of the low-degree test, and `m' + 6` `m'`-variate polynomials `c`, the codewords of the sixth copy. Its honest answer to a question of type `(i, τ)` (`honestAns`) is the honest answer…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.AnswerReduction
--   open Finset MIPRE.LIDT MIPRE.LIDT.CL MIPRE.SAT MIPRE.AnswerReduction.Pcp
--   variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
--   variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
--   variable {X : Type*} (check : X → (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool)
--
--   theorem MIPRE.AnswerReduction.side_honest (tp tq : Role × PcpTy) (xp xq : X) (w : Coord P → F) (Hp Hq : HPolys P F)
--       (hp : Hp.LowDeg) (hpo : tp.1 = .oracle → Hp.Oracle (check xp))
--       (hc : Consistent tp.1 tq.1 Hp Hq) :
--       side S S' check (tp, xp, (pres P S S' tp.2).eval w) (tq, xq, (pres P S S' tq.2).eval w)
--         (honestAns S S' Hp tp.2 ((pres P S S' tp.2).eval w))
--         (honestAns S S' Hq tq.2 ((pres P S S' tq.2).eval w)) = true
--   ```
--
--   **Formalization Note** `MIPRE.AnswerReduction.side_honest` is declared in `MIPRE/Background/AnswerReduction/Honest.lean`, lines 221–295. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/Honest.lean#L221-L295; blueprint lem:ar-completeness

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpPresentation
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Background_AnswerReduction_Predicate
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_CLHonest
import Definitions.Def_MIPRE_Background_AnswerReduction_Honest

open MIPRE
open MIPRE.AnswerReduction
open Finset MIPRE.LIDT MIPRE.LIDT.CL MIPRE.SAT MIPRE.AnswerReduction.Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
variable {X : Type*} (check : X → (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool)

theorem MIPRE.AnswerReduction.side_honest (tp tq : Role × PcpTy) (xp xq : X) (w : Coord P → F) (Hp Hq : HPolys P F)
    (hp : Hp.LowDeg) (hpo : tp.1 = .oracle → Hp.Oracle (check xp))
    (hc : Consistent tp.1 tq.1 Hp Hq) :
    side S S' check (tp, xp, (pres P S S' tp.2).eval w) (tq, xq, (pres P S S' tq.2).eval w)
      (honestAns S S' Hp tp.2 ((pres P S S' tp.2).eval w))
      (honestAns S S' Hq tq.2 ((pres P S S' tq.2).eval w)) = true := by sorry
