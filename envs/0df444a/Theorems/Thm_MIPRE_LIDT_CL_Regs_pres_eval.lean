-- Prove2me | Theorems.Thm_MIPRE_LIDT_CL_Regs_pres_eval
-- name    : MIPRE.LIDT.CL.Regs.pres_eval
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:11:57.647611+00:00
-- url     : https://prove2.me/theorems/258bc5a5-edce-4eab-b579-52202fe79389
-- title:
--   The presentation's output is the embedding of the question it computes
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.PresentationEmbed` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The presentation's output is a function of its question. Piece AR-5b of `planning/answer-reduction.md` needs the converse of `Regs.questionOf_eval`: the vector a type's presentation outputs is supported on the copy's own registers, and is a fixed function (`Regs.embedQ`) of the seeded question it computes (`Regs.pres_eval`). So a strategy that answers a question vector of the answer-reduced verifier answers, through `embedQ`, the seeded low-degree test's question, and the two games' questions correspond one to one.
--
--   **The presentation's output is the embedding of the question it computes.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.CL
--   open MIPRE.LIDT.CL.Regs
--   open Finset MIPRE.CL
--   variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
--
--   theorem MIPRE.LIDT.CL.Regs.pres_eval (t : Ty) (x : ι → F) :
--       (R.pres S t).eval x = R.embedQ S ((R.sampleOf S t x).question hn t)
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.CL.Regs.pres_eval` is declared in `MIPRE/Background/LIDT/PresentationEmbed.lean`, lines 57–84. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/PresentationEmbed.lean#L57-L84

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_CLHonest
import Definitions.Def_MIPRE_Background_LIDT_PresentationEmbed

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.CL
open MIPRE.LIDT.CL.Regs
open Finset MIPRE.CL
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)

theorem MIPRE.LIDT.CL.Regs.pres_eval (t : Ty) (x : ι → F) :
    (R.pres S t).eval x = R.embedQ S ((R.sampleOf S t x).question hn t) := by sorry
