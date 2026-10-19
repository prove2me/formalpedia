-- Prove2me | Theorems.Thm_MIPRE_LIDT_CL_accepts_honest
-- name    : MIPRE.LIDT.CL.accepts_honest
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:03:02.341989+00:00
-- url     : https://prove2.me/theorems/62dbc0e1-3786-4595-944b-db1f4cb24636
-- title:
--   The seeded CL test accepts honest answers to the two questions of a sample, for any tuple of polynomials of individual degree at most d
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.CLHonest` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Honest answers in the seeded CL low-degree test. Piece AR-4 of `planning/answer-reduction.md` needs the completeness of the seeded CL test (`def:lidt-cl`, `MIPRE.LIDT.CL.accepts`): a tuple of polynomials of individual degree at most `d`, answered honestly — its values at a point, its restrictions to a line — passes the test on any two questions of one sample. * `honest` — the honest answer of a tuple `G` of `ldc` polynomials to a question: the values at a point, the coefficients of the restrictions (`MIPRE.LowDegree.lineRestrict`) to an axis-parallel or diagonal line. * `accepts_honest` — the…
--
--   **The seeded CL test accepts honest answers** to the two questions of a sample, for any tuple
--   of polynomials of individual degree at most `d`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.CL
--   open Finset MIPRE.CL MIPRE.LowDegree
--   variable {F : Type*} [Field F] {m : ℕ}
--   variable [Fintype F] [DecidableEq F] [NeZero m] (hm : m ∣ Fintype.card F) {d ldc : ℕ}
--   variable {hm}
--
--   theorem MIPRE.LIDT.CL.accepts_honest {G : Fin ldc → MvPolynomial (Fin m) F}
--       (hG : ∀ j i, (G j).degreeOf i ≤ d) (sm : Sample F m) (τ τ' : Ty) :
--       accepts hm (sm.question hm τ) (sm.question hm τ')
--         (honest hm (d := d) G (sm.question hm τ)) (honest hm (d := d) G (sm.question hm τ'))
--         = true
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.CL.accepts_honest` is declared in `MIPRE/Background/LIDT/CLHonest.lean`, lines 127–147. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/CLHonest.lean#L127-L147; blueprint lem:ar-completeness

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

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.CL
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
variable [Fintype F] [DecidableEq F] [NeZero m] (hm : m ∣ Fintype.card F) {d ldc : ℕ}
variable {hm}

theorem MIPRE.LIDT.CL.accepts_honest {G : Fin ldc → MvPolynomial (Fin m) F}
    (hG : ∀ j i, (G j).degreeOf i ≤ d) (sm : Sample F m) (τ τ' : Ty) :
    accepts hm (sm.question hm τ) (sm.question hm τ')
      (honest hm (d := d) G (sm.question hm τ)) (honest hm (d := d) G (sm.question hm τ'))
      = true := by sorry
