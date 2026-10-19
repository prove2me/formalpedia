-- Prove2me | Theorems.Thm_MIPRE_SyncStrategy_value_pushQ_eq_one
-- name    : MIPRE.SyncStrategy.value_pushQ_eq_one
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:16:58.656784+00:00
-- url     : https://prove2.me/theorems/796d5c1f-1576-4f9a-a75b-52dff2641445
-- title:
--   The read strategy has value 1. The old strategy's operators for a rejected pair at a pair of positive weight multiply to zero (hZ, the strong form of value 1 that a PCC…
-- statement:
--   A statement of the module `MIPRE.Foundations.SyncPushQ` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Playing a synchronous strategy through a reading of the questions. The honest strategy of a compiled game often measures an old strategy at a question computed from the new one, and post-processes the outcome with a map that may depend on the new question. For answer reduction (AR-4 of `planning/answer-reduction.md`) the old game is the oracularized one: each player measures at the oracularized question its seed's oracle half determines, and answers the low-degree encoding of the outcome that its PCP question asks for. `SyncStrategy.pushQ` is that strategy: at a new question `x'`, the…
--
--   **The read strategy has value `1`.** The old strategy's operators for a rejected pair at a
--   pair of positive weight multiply to zero (`hZ`, the strong form of value `1` that a PCC
--   strategy of value `1` has, e.g. `SeededGame.oracleOp_mul_eq_zero`). Every new pair `(x', y')`
--   of positive weight is read as an old pair of positive weight, and an old answer pair accepted
--   there — with each answer also accepted against itself at its own question, when that pair has
--   positive weight — is read as an accepted new pair.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SyncStrategy
--   open Finset
--   variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A] {G : SynchronousGame X A}
--
--   theorem MIPRE.SyncStrategy.value_pushQ_eq_one (S : SyncStrategy G) {X' A' : Type*} [Fintype X'] [Fintype A']
--       [DecidableEq A'] (G' : SynchronousGame X' A') (g : X' → X) (f : X' → A → A')
--       (hZ : ∀ x y, 0 < G.μ x y → ∀ a b, G.D x y a b = false → S.P.M x a * S.P.M y b = 0)
--       (h : ∀ x' y', 0 < G'.μ x' y' → 0 < G.μ (g x') (g y') ∧ ∀ a b,
--         (0 < G.μ (g x') (g x') → G.D (g x') (g x') a a = true) →
--         (0 < G.μ (g y') (g y') → G.D (g y') (g y') b b = true) →
--         G.D (g x') (g y') a b = true → G'.D x' y' (f x' a) (f y' b) = true) :
--       (S.pushQ G' g f).value = 1
--   ```
--
--   **Formalization Note** `MIPRE.SyncStrategy.value_pushQ_eq_one` is declared in `MIPRE/Foundations/SyncPushQ.lean`, lines 86–126. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SyncPushQ.lean#L86-L126; blueprint lem:ar-completeness

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
import Definitions.Def_MIPRE_Foundations_SyncPushQ

open MIPRE
open MIPRE.SyncStrategy
open Finset
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A] {G : SynchronousGame X A}

theorem MIPRE.SyncStrategy.value_pushQ_eq_one (S : SyncStrategy G) {X' A' : Type*} [Fintype X'] [Fintype A']
    [DecidableEq A'] (G' : SynchronousGame X' A') (g : X' → X) (f : X' → A → A')
    (hZ : ∀ x y, 0 < G.μ x y → ∀ a b, G.D x y a b = false → S.P.M x a * S.P.M y b = 0)
    (h : ∀ x' y', 0 < G'.μ x' y' → 0 < G.μ (g x') (g y') ∧ ∀ a b,
      (0 < G.μ (g x') (g x') → G.D (g x') (g x') a a = true) →
      (0 < G.μ (g y') (g y') → G.D (g y') (g y') b b = true) →
      G.D (g x') (g y') a b = true → G'.D x' y' (f x' a) (f y' b) = true) :
    (S.pushQ G' g f).value = 1 := by sorry
