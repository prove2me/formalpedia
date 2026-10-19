-- Prove2me | Theorems.Thm_MIPRE_SeededGame_oracleOp_mul_eq_zero
-- name    : MIPRE.SeededGame.oracleOp_mul_eq_zero
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:15:17.854596+00:00
-- url     : https://prove2.me/theorems/2a516c33-9e07-4b03-beb7-7a9e6fde479b
-- title:
--   No rejected outcome. At any question pair of positive weight, the honest operators for a rejected answer pair multiply to zero
-- statement:
--   A statement of the module `MIPRE.Foundations.OracularComplete` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Completeness of oracularization. Item 1 of blueprint `thm:oracularization`: a value-`1` PCC strategy for the input game gives one for the oracularized game of `MIPRE.SeededGame.oracular`. The honest oracle measures the input strategy's *two* measurements jointly: at seed `z` its operator for the answer pair `(a, b)` is `M^{(false, L^𝖠 z)}_a · M^{(true, L^𝖡 z)}_b`. That product is a projection exactly because the two commute, which is what `IsPCC` supplies at the question pair the seed determines — and the seed always determines a pair of positive weight, since `z` itself lies in its fibre…
--
--   **No rejected outcome.** At any question pair of positive weight, the honest operators for
--   a rejected answer pair multiply to zero.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SeededGame
--   open Finset Matrix
--   variable {V A : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
--   variable (S : SeededGame V A)
--   variable {S}
--   variable (S)
--   variable {S}
--   variable (S)
--   variable {S}
--
--   theorem MIPRE.SeededGame.oracleOp_mul_eq_zero (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC)
--       (hval : T.value = 1) {p q : Role × V} (hμ : 0 < S.oDist p q) {u v : OAns A}
--       (hrej : S.oaccepts p q u v = false) :
--       S.oracleOp T p u * S.oracleOp T q v = 0
--   ```
--
--   **Formalization Note** `MIPRE.SeededGame.oracleOp_mul_eq_zero` is declared in `MIPRE/Foundations/OracularComplete.lean`, lines 273–307. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OracularComplete.lean#L273-L307

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
import Definitions.Def_MIPRE_Foundations_OracularComplete

open MIPRE
open MIPRE.SeededGame
open Finset Matrix
variable {V A : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)
variable {S}
variable (S)
variable {S}
variable (S)
variable {S}

theorem MIPRE.SeededGame.oracleOp_mul_eq_zero (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC)
    (hval : T.value = 1) {p q : Role × V} (hμ : 0 < S.oDist p q) {u v : OAns A}
    (hrej : S.oaccepts p q u v = false) :
    S.oracleOp T p u * S.oracleOp T q v = 0 := by sorry
