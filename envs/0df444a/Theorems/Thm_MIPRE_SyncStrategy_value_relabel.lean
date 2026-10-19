-- Prove2me | Theorems.Thm_MIPRE_SyncStrategy_value_relabel
-- name    : MIPRE.SyncStrategy.value_relabel
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:22:39.380874+00:00
-- url     : https://prove2.me/theorems/b42b7f48-58ff-45a5-b80f-f4a001bc2b56
-- title:
--   Relabeling along equivalences with matching distribution and decision predicate preserves the value
-- statement:
--   A statement of the module `MIPRE.Foundations.GameTransport` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Transport of games and strategies. Bookkeeping lemmas about the quantum value under changes of presentation of a game, used to identify a verifier's game with its tabulation as a game description and to compare the same game under different answer-length bounds (blueprint `rem:compression-abstract`): * **Relabeling.** `quantumValue_eq_of_equiv`: two games related by equivalences of their four alphabets, with matching distribution and decision predicate, have the same quantum value. Strategies are transported by `TensorProductStrategy.relabel`. * **Monotonicity.** `quantumValue_mono`:…
--
--   Relabeling along equivalences with matching distribution and decision predicate
--   preserves the value.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SyncStrategy
--   open Matrix Kronecker
--   open scoped ComplexOrder
--   variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
--   variable [DecidableEq A] {G : SynchronousGame X A}
--
--   theorem MIPRE.SyncStrategy.value_relabel {X' A' : Type*} [Fintype X'] [Fintype A'] [DecidableEq A']
--       (S : SyncStrategy G) (G' : SynchronousGame X' A') (eX : X' ≃ X) (eA : A' ≃ A)
--       (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eX y'))
--       (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eX y') (eA a') (eA b')) :
--       (S.relabel G' eX eA).value = S.value
--   ```
--
--   **Formalization Note** `MIPRE.SyncStrategy.value_relabel` is declared in `MIPRE/Foundations/GameTransport.lean`, lines 469–484. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameTransport.lean#L469-L484

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport

open MIPRE
open MIPRE.SyncStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] {G : SynchronousGame X A}

theorem MIPRE.SyncStrategy.value_relabel {X' A' : Type*} [Fintype X'] [Fintype A'] [DecidableEq A']
    (S : SyncStrategy G) (G' : SynchronousGame X' A') (eX : X' ≃ X) (eA : A' ≃ A)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eX y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eX y') (eA a') (eA b')) :
    (S.relabel G' eX eA).value = S.value := by sorry
