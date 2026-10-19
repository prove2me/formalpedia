-- Prove2me | Theorems.Thm_MIPRE_LowDegree_natDegree_lineRestrict_single_le
-- name    : MIPRE.LowDegree.natDegree_lineRestrict_single_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:23:38.206514+00:00
-- url     : https://prove2.me/theorems/4e765089-cf09-4556-9a21-12ca0afce815
-- title:
--   On an axis-parallel line the restriction has degree at most the individual degree in that coordinate. Along u_0 + t e_j only the j-th variable moves, so every other…
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.LineRestrict` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Restricting a polynomial to a line. The expansion stage's line measurements are indexed by the *restriction to a line* of the low-degree encoding of the ancilla's measurement outcome. This file is that operation: substitute the affine parametrization `t -> u0 + t . w` into a multivariate polynomial and read off the univariate coefficients. Two facts are all the consumers need: * `eval_lineRestrict` --- evaluating the restriction at `t` is evaluating the polynomial at the point `u0 + t . w`, so the restriction carries the same information along the line; * `natDegree_lineRestrict_le` --- the…
--
--   **On an axis-parallel line the restriction has degree at most the individual degree in that
--   coordinate.** Along `u_0 + t e_j` only the `j`-th variable moves, so every other substitution is a
--   constant and the degree in `t` is the degree of `p` in `X_j`. This is what makes a *multilinear*
--   encoding restrict to an affine function of the line parameter.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open Finset
--   variable {F : Type*} [Field F] {m : ℕ}
--
--   theorem MIPRE.LowDegree.natDegree_lineRestrict_single_le (u₀ : Fin m → F) (j : Fin m)
--       (p : MvPolynomial (Fin m) F) :
--       (lineRestrict u₀ (Pi.single j 1) p).natDegree ≤ p.degreeOf j
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.natDegree_lineRestrict_single_le` is declared in `MIPRE/Foundations/LowDegree/LineRestrict.lean`, lines 83–118. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/LineRestrict.lean#L83-L118; blueprint lem:qld-axis-degree

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict

open MIPRE
open MIPRE.LowDegree
open Finset
variable {F : Type*} [Field F] {m : ℕ}

theorem MIPRE.LowDegree.natDegree_lineRestrict_single_le (u₀ : Fin m → F) (j : Fin m)
    (p : MvPolynomial (Fin m) F) :
    (lineRestrict u₀ (Pi.single j 1) p).natDegree ≤ p.degreeOf j := by sorry
