-- Prove2me | Theorems.Thm_MIPRE_SyncStrategy_value_le_copy
-- name    : MIPRE.SyncStrategy.value_le_copy
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:56:44.938372+00:00
-- url     : https://prove2.me/theorems/cf26f623-bb10-4774-ac07-7d7cb49ed20e
-- title:
--   Relaxing a predicate with the same question law can only increase a copied synchronous strategy's value
-- statement:
--   A statement of the module `MIPRE.Foundations.GameTransportByQuestion` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Merging strategy answers separately at each question. Deterministic answer decoding can depend on the question. Merging the fibers of these maps preserves projectivity, register dimensions and the shared state. Acceptance implication gives monotonicity of the resulting value.
--
--   Relaxing a predicate with the same question law can only increase a copied
--   synchronous strategy's value.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SyncStrategy
--   open Matrix Kronecker Finset Classical
--   variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
--
--   theorem MIPRE.SyncStrategy.value_le_copy (S : SyncStrategy G) (G' : SynchronousGame X A)
--       (hμ : ∀ x y, G'.μ x y = G.μ x y)
--       (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true) :
--       S.value ≤ (S.copy G').value
--   ```
--
--   **Formalization Note** `MIPRE.SyncStrategy.value_le_copy` is declared in `MIPRE/Foundations/GameTransportByQuestion.lean`, lines 157–175. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameTransportByQuestion.lean#L157-L175

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
open MIPRE.SyncStrategy
open Matrix Kronecker Finset Classical
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  {G : SynchronousGame X A}

theorem MIPRE.SyncStrategy.value_le_copy (S : SyncStrategy G) (G' : SynchronousGame X A)
    (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true) :
    S.value ≤ (S.copy G').value := by sorry
