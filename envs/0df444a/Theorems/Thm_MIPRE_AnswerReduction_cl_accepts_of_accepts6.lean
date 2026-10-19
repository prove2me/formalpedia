-- Prove2me | Theorems.Thm_MIPRE_AnswerReduction_cl_accepts_of_accepts6
-- name    : MIPRE.AnswerReduction.cl_accepts_of_accepts6
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:00:38.170257+00:00
-- url     : https://prove2.me/theorems/fff25731-6b1d-40fa-b333-268ad140ff82
-- title:
--   The sixth copy's test inside the predicate, for two oracles
-- statement:
--   A statement of the module `MIPRE.Background.AnswerReduction.SoundCopy` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Soundness of answer reduction: the low-degree test inside the predicate. Piece AR-5b of `planning/answer-reduction.md` (`claim:ar-3`, `claim:ar-4`): on the nine type pairs of one copy of the low-degree test, at a role pair where the answer-reduced predicate runs that copy's test, acceptance of the predicate implies acceptance of the seeded CL test on the questions the copy's presentation computes (`cl_accepts_of_accepts`, `cl_accepts_of_accepts6`). The copies tested are copy `v` for the isolated player `v` (step 3), copies `3`, `4`, `5` and the sixth for two oracles (step 4); an oracle's…
--
--   **The sixth copy's test inside the predicate**, for two oracles.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.AnswerReduction
--   open Finset MIPRE.LIDT MIPRE.LIDT.CL MIPRE.SAT MIPRE.AnswerReduction.Pcp
--   variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero P.m]
--
--   theorem MIPRE.AnswerReduction.cl_accepts_of_accepts6 {i : Fin 6} (hi : (i : ℕ) = 5) (τ τ' : Ty) {x x' : X}
--       {y y' : Coord P → F} {u v : Ans P F}
--       (h : accepts S S' check ((.oracle, (i, τ)), x, y) ((.oracle, (i, τ')), x', y') u v = true) :
--       CL.accepts hm' (q6 S' τ y) (q6 S' τ' y') (ans6 u) (ans6 v) = true
--   ```
--
--   **Formalization Note** `MIPRE.AnswerReduction.cl_accepts_of_accepts6` is declared in `MIPRE/Background/AnswerReduction/SoundCopy.lean`, lines 136–161. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/SoundCopy.lean#L136-L161

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
import Definitions.Def_MIPRE_Background_LIDT_PresentationEmbed
import Definitions.Def_MIPRE_Background_AnswerReduction_SoundCopy

open MIPRE
open MIPRE.AnswerReduction
open Finset MIPRE.LIDT MIPRE.LIDT.CL MIPRE.SAT MIPRE.AnswerReduction.Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero P.m]
  {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F} (S : Sel F P.m hm)
  (S' : Sel F P.m' hm') {X : Type*} (check : X → (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool)

theorem MIPRE.AnswerReduction.cl_accepts_of_accepts6 {i : Fin 6} (hi : (i : ℕ) = 5) (τ τ' : Ty) {x x' : X}
    {y y' : Coord P → F} {u v : Ans P F}
    (h : accepts S S' check ((.oracle, (i, τ)), x, y) ((.oracle, (i, τ')), x', y') u v = true) :
    CL.accepts hm' (q6 S' τ y) (q6 S' τ' y') (ans6 u) (ans6 v) = true := by sorry
