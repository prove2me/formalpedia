-- Prove2me | Theorems.Thm_MIPRE_sum_bornProb_map
-- name    : MIPRE.sum_bornProb_map
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:21:29.848991+00:00
-- url     : https://prove2.me/theorems/094dc688-b328-4be3-9ac0-be39fa7ecc1a
-- title:
--   The agreement probability of the coarse-grained POVMs, as a sum over the original outcome pairs
-- statement:
--   A statement of the module `MIPRE.Foundations.CrossConsistency` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Cross-party consistency, and what winning a subtest buys. The Pauli appendix's `≃_δ` compares `A ⊗ Id` with `Id ⊗ B`: one player's operator against the *other* player's. `MIPRE.stateDist` of `def:state-distance` compares two families on the same side, which is what the orthonormalization step needs; this file is the cross-party form, and the one lemma that produces it.
--
--   The agreement probability of the coarse-grained POVMs, as a sum over the original outcome
--   pairs.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix Kronecker
--   open scoped ComplexOrder MatrixOrder
--   variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
--   variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
--
--   theorem MIPRE.sum_bornProb_map {x : X} {y : Y} (f : A → C) (g : B → C) :
--       ∑ c, bornProb ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val)
--         = ∑ a, ∑ b, (if f a = g b then (1 : ℝ) else 0)
--             * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val)
--   ```
--
--   **Formalization Note** `MIPRE.sum_bornProb_map` is declared in `MIPRE/Foundations/CrossConsistency.lean`, lines 235–272. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CrossConsistency.lean#L235-L272; blueprint def:cross-distance

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency

open MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
omit [Fintype X] [Fintype Y]

theorem MIPRE.sum_bornProb_map {x : X} {y : Y} (f : A → C) (g : B → C) :
    ∑ c, bornProb ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val)
      = ∑ a, ∑ b, (if f a = g b then (1 : ℝ) else 0)
          * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by sorry
