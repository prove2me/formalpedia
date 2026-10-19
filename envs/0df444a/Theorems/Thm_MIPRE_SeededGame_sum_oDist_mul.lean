-- Prove2me | Theorems.Thm_MIPRE_SeededGame_sum_oDist_mul
-- name    : MIPRE.SeededGame.sum_oDist_mul
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:15:17.319711+00:00
-- url     : https://prove2.me/theorems/a8e4a50a-bffc-4b18-bfd4-ac2e21a34535
-- title:
--   The oracularized game's distribution, against a test function: an average over the ordered pair of roles and the seed
-- statement:
--   A statement of the module `MIPRE.Foundations.OracularSound` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Soundness of oracularization. Item 2 of blueprint `thm:oracularization` (`lem:oracular-soundness`), at the level of games: a synchronous strategy of value at least `1 - ε` for `MIPRE.SeededGame.oracular` yields one of value at least `1 - 24√ε` for the doubled input game. The loss carries the **single square root** that repair 1 of `rem:oracularization-repairs` insists on -- an earlier revision of the blueprint wrote `poly(ε)`, which the campaign found "not merely imprecise but false as stated". It is spent in exactly one place, `MIPRE.sum_ntr_mul_ge`; everything before it is linear in `ε`.
--
--   The oracularized game's distribution, against a test function: an average over the ordered
--   pair of roles and the seed.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SeededGame
--   open Finset Matrix
--   variable {A : Type*} [Inhabited A]
--   variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
--   variable (S : SeededGame V A)
--
--   theorem MIPRE.SeededGame.sum_oDist_mul (F : Role × V → Role × V → ℝ) :
--       ∑ p, ∑ q, S.oDist p q * F p q
--         = (Fintype.card (Role × Role × V) : ℝ)⁻¹ *
--           ∑ s : Role × Role × V, F (S.oquestion s.1 s.2.2) (S.oquestion s.2.1 s.2.2)
--   ```
--
--   **Formalization Note** `MIPRE.SeededGame.sum_oDist_mul` is declared in `MIPRE/Foundations/OracularSound.lean`, lines 107–125. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OracularSound.lean#L107-L125

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound

open MIPRE
open MIPRE.SeededGame
open Finset Matrix
variable {A : Type*} [Inhabited A]
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)
omit [Nonempty V] [Fintype A] [DecidableEq A] [Inhabited A]

theorem MIPRE.SeededGame.sum_oDist_mul (F : Role × V → Role × V → ℝ) :
    ∑ p, ∑ q, S.oDist p q * F p q
      = (Fintype.card (Role × Role × V) : ℝ)⁻¹ *
        ∑ s : Role × Role × V, F (S.oquestion s.1 s.2.2) (S.oquestion s.2.1 s.2.2) := by sorry
