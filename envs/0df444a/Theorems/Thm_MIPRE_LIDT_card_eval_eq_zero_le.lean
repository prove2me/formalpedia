-- Prove2me | Theorems.Thm_MIPRE_LIDT_card_eval_eq_zero_le
-- name    : MIPRE.LIDT.card_eval_eq_zero_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T23:15:03.505239+00:00
-- url     : https://prove2.me/theorems/a5ada8df-1ca9-4a37-a1a6-9b61f0fe8d19
-- title:
--   Schwartz--Zippel for a nonzero coefficient vector: it vanishes at a uniform point with probability at most n d / q
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Coefficients` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Coefficient vectors of low-individual-degree polynomials. `LowIndDegPoly F n d` is a coefficient vector indexed by exponent vectors with entries at most `d`. This file is the algebra of those vectors that more than one analysis needs, moved here from the Pauli basis test's `Dummy.lean` and `Linear.lean` (where it was first written) so that the simultaneous low-degree test, which sits below the Pauli test in the import graph, can use it. The names are unchanged. * **Schwartz--Zippel for any finite variable type** (`prob_agreeOn_le_individualDegree`), and the bridge `LowIndDegPoly.toMv` to…
--
--   **Schwartz--Zippel for a nonzero coefficient vector**: it vanishes at a uniform point with
--   probability at most `n d / q`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open Finset
--   variable {F : Type*} [Field F] {n d : ℕ}
--
--   theorem MIPRE.LIDT.card_eval_eq_zero_le [Fintype F] [DecidableEq F]
--       {G : LowIndDegPoly (F := F) (m := n) (d := d)} (hG : G ≠ 0) :
--       ((univ.filter fun u : Point F n => G.eval u = 0).card : ℝ) / (Fintype.card F : ℝ) ^ n
--         ≤ (n : ℝ) * d / Fintype.card F
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.card_eval_eq_zero_le` is declared in `MIPRE/Background/LIDT/Coefficients.lean`, lines 302–322. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Coefficients.lean#L302-L322; blueprint lem:lidt-ldc-extraction

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

open MIPRE
open MIPRE.LIDT
open Finset
variable {F : Type*} [Field F] {n d : ℕ}

theorem MIPRE.LIDT.card_eval_eq_zero_le [Fintype F] [DecidableEq F]
    {G : LowIndDegPoly (F := F) (m := n) (d := d)} (hG : G ≠ 0) :
    ((univ.filter fun u : Point F n => G.eval u = 0).card : ℝ) / (Fintype.card F : ℝ) ^ n
      ≤ (n : ℝ) * d / Fintype.card F := by sorry
