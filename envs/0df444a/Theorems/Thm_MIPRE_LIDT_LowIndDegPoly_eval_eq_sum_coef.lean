-- Prove2me | Theorems.Thm_MIPRE_LIDT_LowIndDegPoly_eval_eq_sum_coef
-- name    : MIPRE.LIDT.LowIndDegPoly.eval_eq_sum_coef
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:52:00.02206+00:00
-- url     : https://prove2.me/theorems/20dc08fd-ae30-4fcf-b80a-23bddcf1c9e2
-- title:
--   Decomposition along the patterns on T: g(u) = ∑_t u^t_T · (coef g T t)(u)
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Coefficients` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Coefficient vectors of low-individual-degree polynomials. `LowIndDegPoly F n d` is a coefficient vector indexed by exponent vectors with entries at most `d`. This file is the algebra of those vectors that more than one analysis needs, moved here from the Pauli basis test's `Dummy.lean` and `Linear.lean` (where it was first written) so that the simultaneous low-degree test, which sits below the Pauli test in the import graph, can use it. The names are unchanged. * **Schwartz--Zippel for any finite variable type** (`prob_agreeOn_le_individualDegree`), and the bridge `LowIndDegPoly.toMv` to…
--
--   **Decomposition along the patterns on `T`**: `g(u) = ∑_t u^t_T · (coef g T t)(u)`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.LowIndDegPoly
--   open Finset
--   variable {F : Type*} [Field F] {n d : ℕ}
--
--   theorem MIPRE.LIDT.LowIndDegPoly.eval_eq_sum_coef (g : LowIndDegPoly (F := F) (m := n) (d := d))
--       (T : Finset (Fin n)) (u : Point F n) :
--       g.eval u = ∑ t : Fin n → Fin (d + 1), (∏ k ∈ T, u k ^ (t k : ℕ)) * (g.coef T t).eval u
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.LowIndDegPoly.eval_eq_sum_coef` is declared in `MIPRE/Background/LIDT/Coefficients.lean`, lines 231–276. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Coefficients.lean#L231-L276; blueprint lem:lidt-ldc-extraction

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Coefficients_B

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.LowIndDegPoly
open Finset
variable {F : Type*} [Field F] {n d : ℕ}

theorem MIPRE.LIDT.LowIndDegPoly.eval_eq_sum_coef (g : LowIndDegPoly (F := F) (m := n) (d := d))
    (T : Finset (Fin n)) (u : Point F n) :
    g.eval u = ∑ t : Fin n → Fin (d + 1), (∏ k ∈ T, u k ^ (t k : ℕ)) * (g.coef T t).eval u := by sorry
