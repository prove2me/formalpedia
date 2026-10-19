-- Prove2me | Theorems.Thm_MIPRE_sum_pi_prod
-- name    : MIPRE.sum_pi_prod
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:43:57.655528+00:00
-- url     : https://prove2.me/theorems/e55ac6b1-6394-454b-ba08-c784f49065c5
-- title:
--   A sum over k-tuples of a product of per-coordinate terms is the k-th power of the single-coordinate sum
-- statement:
--   A statement of the module `MIPRE.Background.Repetition.TensorPower` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Tensor powers of synchronous strategies. The completeness half of `thm:parallel-repetition` at the level of games: the `k`-fold tensor power of a PCC synchronous strategy of value `1` is a PCC synchronous strategy of value `1` for the `k`-fold direct repetition (blueprint `def:direct-repetition`). * `ProjectiveMeasurement.tensorPow P k`: the family `x⃗ ↦ a⃗ ↦ ⊗ᵢ M^{xᵢ}_{aᵢ}` on `ℂ^{Fin k → Fin d}` (`MIPRE.tensorFamily`), a projective measurement family on the repeated alphabets; `ProjectiveMeasurement.reindexMat` carries it to `ℂ^{d^k}`, the shape `SyncStrategy` asks for. *…
--
--   A sum over `k`-tuples of a product of per-coordinate terms is the `k`-th power of the
--   single-coordinate sum.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Matrix
--   variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
--
--   theorem MIPRE.sum_pi_prod {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
--       (f : X → Y → A → B → ℝ) (k : ℕ) :
--       (∑ x : Fin k → X, ∑ y : Fin k → Y, ∑ a : Fin k → A, ∑ b : Fin k → B,
--           ∏ i, f (x i) (y i) (a i) (b i)) =
--         (∑ x, ∑ y, ∑ a, ∑ b, f x y a b) ^ k
--   ```
--
--   **Formalization Note** `MIPRE.sum_pi_prod` is declared in `MIPRE/Background/Repetition/TensorPower.lean`, lines 134–163. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Repetition/TensorPower.lean#L134-L163

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Background_Repetition_Direct
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_TensorFamily
import Definitions.Def_MIPRE_Background_Repetition_TensorPower

open MIPRE
open Matrix
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]

theorem MIPRE.sum_pi_prod {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (f : X → Y → A → B → ℝ) (k : ℕ) :
    (∑ x : Fin k → X, ∑ y : Fin k → Y, ∑ a : Fin k → A, ∑ b : Fin k → B,
        ∏ i, f (x i) (y i) (a i) (b i)) =
      (∑ x, ∑ y, ∑ a, ∑ b, f x y a b) ^ k := by sorry
