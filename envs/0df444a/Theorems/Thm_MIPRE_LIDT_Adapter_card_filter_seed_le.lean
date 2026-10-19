-- Prove2me | Theorems.Thm_MIPRE_LIDT_Adapter_card_filter_seed_le
-- name    : MIPRE.LIDT.Adapter.card_filter_seed_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:01:39.263198+00:00
-- url     : https://prove2.me/theorems/ccb6d7dc-53b2-4935-b8c4-017b23d686c4
-- title:
--   A pinned seed index costs a factor q/m
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Adapter.Weights` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded-CL adapter, part 5: both tests' distributions, as counts. The reduction's remaining obligation is a push-forward bound between the two tests' question distributions, and both are defined as sums over a `Sample` type against an indicator. So the first thing to do is to turn each into a *count*, after which the bound is arithmetic on cardinalities rather than on sums. * `clGame`'s distribution is uniform over its samples, so it is the number of samples producing the question pair, over the total (`clGame_μ_eq`). * `lidtGame`'s is not uniform — its three subtests are weighted `1/3`…
--
--   **A pinned seed index costs a factor `q/m`.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.Adapter
--   open Finset MIPRE.LIDT MIPRE.LIDT.CL
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
--
--   theorem MIPRE.LIDT.Adapter.card_filter_seed_le (hm : m ∣ Fintype.card F) (i : Fin m) (s₀ : F)
--       (P : Seed F m → Prop) [DecidablePred P]
--       (hP : ∀ σc, P σc → seedOf hm i (σc.1 i) = s₀) :
--       (Finset.univ.filter P).card
--         ≤ (Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1)
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.Adapter.card_filter_seed_le` is declared in `MIPRE/Background/LIDT/Adapter/Weights.lean`, lines 735–759. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Weights.lean#L735-L759

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Weights

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [NeZero m]

theorem MIPRE.LIDT.Adapter.card_filter_seed_le (hm : m ∣ Fintype.card F) (i : Fin m) (s₀ : F)
    (P : Seed F m → Prop) [DecidablePred P]
    (hP : ∀ σc, P σc → seedOf hm i (σc.1 i) = s₀) :
    (Finset.univ.filter P).card
      ≤ (Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1) := by sorry
