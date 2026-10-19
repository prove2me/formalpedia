-- Prove2me | Theorems.Thm_MIPRE_quantumValue_eq_of_equiv
-- name    : MIPRE.quantumValue_eq_of_equiv
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:22:39.453815+00:00
-- url     : https://prove2.me/theorems/9405a50a-a859-458f-97ea-dd98a214d640
-- title:
--   Games related by equivalences of their alphabets, with matching distribution and decision predicate, have the same quantum value
-- statement:
--   A statement of the module `MIPRE.Foundations.GameTransport` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Transport of games and strategies. Bookkeeping lemmas about the quantum value under changes of presentation of a game, used to identify a verifier's game with its tabulation as a game description and to compare the same game under different answer-length bounds (blueprint `rem:compression-abstract`): * **Relabeling.** `quantumValue_eq_of_equiv`: two games related by equivalences of their four alphabets, with matching distribution and decision predicate, have the same quantum value. Strategies are transported by `TensorProductStrategy.relabel`. * **Monotonicity.** `quantumValue_mono`:…
--
--   Games related by equivalences of their alphabets, with matching distribution and
--   decision predicate, have the same quantum value.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Matrix Kronecker
--   open scoped ComplexOrder
--   variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
--
--   theorem MIPRE.quantumValue_eq_of_equiv {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A']
--       [Fintype B'] (G : Game X Y A B) (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y)
--       (eA : A' ≃ A) (eB : B' ≃ B)
--       (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
--       (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
--       quantumValue G' = quantumValue G
--   ```
--
--   **Formalization Note** `MIPRE.quantumValue_eq_of_equiv` is declared in `MIPRE/Foundations/GameTransport.lean`, lines 322–339. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameTransport.lean#L322-L339

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport

open MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem MIPRE.quantumValue_eq_of_equiv {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A']
    [Fintype B'] (G : Game X Y A B) (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y)
    (eA : A' ≃ A) (eB : B' ≃ B)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
    quantumValue G' = quantumValue G := by sorry
