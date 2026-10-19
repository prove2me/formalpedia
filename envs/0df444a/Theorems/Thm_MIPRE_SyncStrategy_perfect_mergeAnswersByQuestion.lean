-- Prove2me | Theorems.Thm_MIPRE_SyncStrategy_perfect_mergeAnswersByQuestion
-- name    : MIPRE.SyncStrategy.perfect_mergeAnswersByQuestion
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:47:24.905726+00:00
-- url     : https://prove2.me/theorems/b58ca50e-458c-40a9-9394-cd6ad9da3a88
-- title:
--   Perfect play survives any encoder that preserves accepted supported pairs
-- statement:
--   A statement of the module `MIPRE.Foundations.SyncMergeByQuestion` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Perfect PCC strategies under question-dependent answer encoding. Answers can be encoded separately at each question. The encoding need only preserve acceptance for nonzero effects on question pairs of positive weight. This allows format and range facts supplied by an honest strategy's support.
--
--   Perfect play survives any encoder that preserves accepted supported pairs.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SyncStrategy
--   open Matrix Finset Classical
--   variable {X A B : Type*} [Fintype X] [Fintype A] [DecidableEq A]
--
--   theorem MIPRE.SyncStrategy.perfect_mergeAnswersByQuestion (S : SyncStrategy G) (H : SynchronousGame X B)
--       (f : X → A → B) (hμ : ∀ x y, H.μ x y = G.μ x y)
--       (hD : ∀ x y a b, 0 < G.μ x y → S.P.M x a ≠ 0 → S.P.M y b ≠ 0 →
--         G.D x y a b = true → H.D x y (f x a) (f y b) = true)
--       (hv : S.value = 1) : (S.mergeAnswersByQuestion H f).value = 1
--   ```
--
--   **Formalization Note** `MIPRE.SyncStrategy.perfect_mergeAnswersByQuestion` is declared in `MIPRE/Foundations/SyncMergeByQuestion.lean`, lines 36–66. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SyncMergeByQuestion.lean#L36-L66

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
import Definitions.Def_MIPRE_Foundations_SyncMergeByQuestion

open MIPRE
open MIPRE.SyncStrategy
open Matrix Finset Classical
variable {X A B : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] {G : SynchronousGame X A}

theorem MIPRE.SyncStrategy.perfect_mergeAnswersByQuestion (S : SyncStrategy G) (H : SynchronousGame X B)
    (f : X → A → B) (hμ : ∀ x y, H.μ x y = G.μ x y)
    (hD : ∀ x y a b, 0 < G.μ x y → S.P.M x a ≠ 0 → S.P.M y b ≠ 0 →
      G.D x y a b = true → H.D x y (f x a) (f y b) = true)
    (hv : S.value = 1) : (S.mergeAnswersByQuestion H f).value = 1 := by sorry
