-- Prove2me | Theorems.Thm_MIPRE_TensorProductStrategy_value_le_mergeAnswersByQuestion
-- name    : MIPRE.TensorProductStrategy.value_le_mergeAnswersByQuestion
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:56:39.629761+00:00
-- url     : https://prove2.me/theorems/f4ac2b63-b0ce-441a-924d-eb5aeed1d705
-- title:
--   Acceptance-preserving answer decoding can only increase the strategy value
-- statement:
--   A statement of the module `MIPRE.Foundations.GameTransportByQuestion` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Merging strategy answers separately at each question. Deterministic answer decoding can depend on the question. Merging the fibers of these maps preserves projectivity, register dimensions and the shared state. Acceptance implication gives monotonicity of the resulting value.
--
--   Acceptance-preserving answer decoding can only increase the strategy value.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TensorProductStrategy
--   open Matrix Kronecker Finset Classical
--   variable {X Y A B A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
--
--   theorem MIPRE.TensorProductStrategy.value_le_mergeAnswersByQuestion {G' : Game X Y A' B'}
--       (S' : TensorProductStrategy G') (G : Game X Y A B)
--       (rA : X → A' → A) (rB : Y → B' → B) (hμ : ∀ x y, G.μ x y = G'.μ x y)
--       (hD : ∀ x y a' b', G'.D x y a' b' = true → G.D x y (rA x a') (rB y b') = true) :
--       S'.value ≤ (S'.mergeAnswersByQuestion G rA rB).value
--   ```
--
--   **Formalization Note** `MIPRE.TensorProductStrategy.value_le_mergeAnswersByQuestion` is declared in `MIPRE/Foundations/GameTransportByQuestion.lean`, lines 52–110. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameTransportByQuestion.lean#L52-L110

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameTransportByQuestion

open MIPRE
open MIPRE.TensorProductStrategy
open Matrix Kronecker Finset Classical
variable {X Y A B A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype A'] [Fintype B'] [DecidableEq A] [DecidableEq B]

theorem MIPRE.TensorProductStrategy.value_le_mergeAnswersByQuestion {G' : Game X Y A' B'}
    (S' : TensorProductStrategy G') (G : Game X Y A B)
    (rA : X → A' → A) (rB : Y → B' → B) (hμ : ∀ x y, G.μ x y = G'.μ x y)
    (hD : ∀ x y a' b', G'.D x y a' b' = true → G.D x y (rA x a') (rB y b') = true) :
    S'.value ≤ (S'.mergeAnswersByQuestion G rA rB).value := by sorry
