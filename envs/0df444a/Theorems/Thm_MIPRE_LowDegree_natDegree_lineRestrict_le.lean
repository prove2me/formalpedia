-- Prove2me | Theorems.Thm_MIPRE_LowDegree_natDegree_lineRestrict_le
-- name    : MIPRE.LowDegree.natDegree_lineRestrict_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:23:34.617284+00:00
-- url     : https://prove2.me/theorems/c458bd0b-5dac-4333-9fcb-405aa3eb41b7
-- title:
--   The restriction has degree at most the total degree
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.LineRestrict` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Restricting a polynomial to a line. The expansion stage's line measurements are indexed by the *restriction to a line* of the low-degree encoding of the ancilla's measurement outcome. This file is that operation: substitute the affine parametrization `t -> u0 + t . w` into a multivariate polynomial and read off the univariate coefficients. Two facts are all the consumers need: * `eval_lineRestrict` --- evaluating the restriction at `t` is evaluating the polynomial at the point `u0 + t . w`, so the restriction carries the same information along the line; * `natDegree_lineRestrict_le` --- the…
--
--   **The restriction has degree at most the total degree.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open Finset
--   variable {F : Type*} [Field F] {m : ℕ}
--
--   theorem MIPRE.LowDegree.natDegree_lineRestrict_le (u₀ w : Fin m → F) (p : MvPolynomial (Fin m) F) :
--       (lineRestrict u₀ w p).natDegree ≤ p.totalDegree
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.natDegree_lineRestrict_le` is declared in `MIPRE/Foundations/LowDegree/LineRestrict.lean`, lines 62–81. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/LineRestrict.lean#L62-L81; blueprint def:line-restriction

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

theorem MIPRE.LowDegree.natDegree_lineRestrict_le (u₀ w : Fin m → F) (p : MvPolynomial (Fin m) F) :
    (lineRestrict u₀ w p).natDegree ≤ p.totalDegree := by sorry
