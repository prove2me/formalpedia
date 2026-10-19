-- Prove2me | Theorems.Thm_MIPRE_xSqNorm_sum_le_two_mul
-- name    : MIPRE.xSqNorm_sum_le_two_mul
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:21:31.841802+00:00
-- url     : https://prove2.me/theorems/e8fda431-3f38-471d-81da-8ca5e5c0a4e3
-- title:
--   From agreement to cross-party closeness. For any two POVMs with the same outcome set, the summed cross-party squared deviation is at most twice the disagreement probability
-- statement:
--   A statement of the module `MIPRE.Foundations.CrossConsistency` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Cross-party consistency, and what winning a subtest buys. The Pauli appendix's `≃_δ` compares `A ⊗ Id` with `Id ⊗ B`: one player's operator against the *other* player's. `MIPRE.stateDist` of `def:state-distance` compares two families on the same side, which is what the orthonormalization step needs; this file is the cross-party form, and the one lemma that produces it.
--
--   **From agreement to cross-party closeness.** For any two POVMs with the same outcome set,
--   the summed cross-party squared deviation is at most twice the disagreement probability. Expand
--   each square: the two diagonal sums are at most one (`sum_stateSqNorm_le_one`), and the cross
--   term is the agreement probability.
--
--   No projectivity, and no hypothesis beyond `ψ` being a unit vector.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix Kronecker
--   open scoped ComplexOrder MatrixOrder
--   variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
--
--   theorem MIPRE.xSqNorm_sum_le_two_mul {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
--       (M : POVM C dA) (N : POVM C dB) :
--       ∑ c, xSqNorm ψ (((M.mats c).val)) (((N.mats c).val))
--         ≤ 2 * (1 - ∑ c, bornProb ψ (((M.mats c).val)) (((N.mats c).val)))
--   ```
--
--   **Formalization Note** `MIPRE.xSqNorm_sum_le_two_mul` is declared in `MIPRE/Foundations/CrossConsistency.lean`, lines 197–223. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CrossConsistency.lean#L197-L223; blueprint def:cross-distance

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
omit [DecidableEq C]

theorem MIPRE.xSqNorm_sum_le_two_mul {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : POVM C dA) (N : POVM C dB) :
    ∑ c, xSqNorm ψ (((M.mats c).val)) (((N.mats c).val))
      ≤ 2 * (1 - ∑ c, bornProb ψ (((M.mats c).val)) (((N.mats c).val))) := by sorry
