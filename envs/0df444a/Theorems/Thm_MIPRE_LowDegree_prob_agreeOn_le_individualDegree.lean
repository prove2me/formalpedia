-- Prove2me | Theorems.Thm_MIPRE_LowDegree_prob_agreeOn_le_individualDegree
-- name    : MIPRE.LowDegree.prob_agreeOn_le_individualDegree
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:52:07.390585+00:00
-- url     : https://prove2.me/theorems/31617c2f-5ef6-45de-b7f0-ba2e90dc42f6
-- title:
--   Schwartz--Zippel, individual-degree form, for any finite variable type: two unequal polynomials of individual degree at most d in the variables σ agree at a uniformly…
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Coefficients` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Coefficient vectors of low-individual-degree polynomials. `LowIndDegPoly F n d` is a coefficient vector indexed by exponent vectors with entries at most `d`. This file is the algebra of those vectors that more than one analysis needs, moved here from the Pauli basis test's `Dummy.lean` and `Linear.lean` (where it was first written) so that the simultaneous low-degree test, which sits below the Pauli test in the import graph, can use it. The names are unchanged. * **Schwartz--Zippel for any finite variable type** (`prob_agreeOn_le_individualDegree`), and the bridge `LowIndDegPoly.toMv` to…
--
--   **Schwartz--Zippel, individual-degree form, for any finite variable type**: two unequal
--   polynomials of individual degree at most `d` in the variables `σ` agree at a uniformly random
--   point of `F^σ` with probability at most `|σ| d / q`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open Finset MvPolynomial
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {σ : Type*} [Fintype σ] [DecidableEq σ]
--
--   theorem MIPRE.LowDegree.prob_agreeOn_le_individualDegree {f g : MvPolynomial σ F} (hfg : f ≠ g) {d : ℕ}
--       (hf : ∀ i, f.degreeOf i ≤ d) (hg : ∀ i, g.degreeOf i ≤ d) :
--       ((agreeOn f g).card : ℝ) / (Fintype.card F : ℝ) ^ Fintype.card σ
--         ≤ (Fintype.card σ : ℝ) * d / Fintype.card F
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.prob_agreeOn_le_individualDegree` is declared in `MIPRE/Background/LIDT/Coefficients.lean`, lines 43–67. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Coefficients.lean#L43-L67; blueprint lem:qld-global-dummy

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
open MIPRE.LowDegree
open Finset MvPolynomial
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem MIPRE.LowDegree.prob_agreeOn_le_individualDegree {f g : MvPolynomial σ F} (hfg : f ≠ g) {d : ℕ}
    (hf : ∀ i, f.degreeOf i ≤ d) (hg : ∀ i, g.degreeOf i ≤ d) :
    ((agreeOn f g).card : ℝ) / (Fintype.card F : ℝ) ^ Fintype.card σ
      ≤ (Fintype.card σ : ℝ) * d / Fintype.card F := by sorry
