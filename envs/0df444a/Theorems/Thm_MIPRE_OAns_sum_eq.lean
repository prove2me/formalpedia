-- Prove2me | Theorems.Thm_MIPRE_OAns_sum_eq
-- name    : MIPRE.OAns.sum_eq
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:24:41.528987+00:00
-- url     : https://prove2.me/theorems/6266ec99-18a0-4b97-bfdb-425108a31522
-- title:
--   A sum over OAns A splits into the pairs and the singles
-- statement:
--   A statement of the module `MIPRE.Foundations.OracularGame` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Oracularization, at the level of games. Blueprint `thm:oracularization` (paper `oracularization.tex`, `sec:orac-def` and `fig:oracle-decider`) turns a normal form verifier into one where a single player --- the *oracle* --- receives the sampler's whole seed and answers *both* original questions, while the other player receives one of the two questions and must answer consistently. That makes the predicate a pointwise function of one player's answer, which is the format answer reduction needs. This file is the construction and its question distribution, at the level of games: no samplers, no…
--
--   A sum over `OAns A` splits into the pairs and the singles.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.OAns
--   open Finset
--   variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
--
--   theorem MIPRE.OAns.sum_eq {M : Type*} [AddCommMonoid M] (f : OAns A → M) :
--       ∑ u, f u = (∑ p : A × A, f (.pair p.1 p.2)) + ∑ a, f (.single a)
--   ```
--
--   **Formalization Note** `MIPRE.OAns.sum_eq` is declared in `MIPRE/Foundations/OracularGame.lean`, lines 146–151. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OracularGame.lean#L146-L151

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_OracularGame

open MIPRE
open MIPRE.OAns
open Finset
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
omit [DecidableEq A]

theorem MIPRE.OAns.sum_eq {M : Type*} [AddCommMonoid M] (f : OAns A → M) :
    ∑ u, f u = (∑ p : A × A, f (.pair p.1 p.2)) + ∑ a, f (.single a) := by sorry
