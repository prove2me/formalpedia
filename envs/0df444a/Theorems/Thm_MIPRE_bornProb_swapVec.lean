-- Prove2me | Theorems.Thm_MIPRE_bornProb_swapVec
-- name    : MIPRE.bornProb_swapVec
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:45.393973+00:00
-- url     : https://prove2.me/theorems/72f08727-c0a5-4030-aa93-59a3d9807c64
-- title:
--   Swapping the state exchanges the two factors of a Born probability
-- statement:
--   A statement of the module `MIPRE.Foundations.Swap` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Exchanging the two players. A game whose question distribution and decision predicate are both symmetric in the players is unchanged by exchanging them, and so is the value of a strategy once the state is swapped (`povmValue_swapVec_of_symm`). That is what turns a one-sided soundness statement --- one proved about Alice's measurements, with Bob's only as the other party --- into the statement about **Bob's**, with no second proof: apply it to `(MB, MA)` on `swapVec ψ`, and read the conclusion back through `norm_stateVecB`. The Pauli basis test is such a game: every rule of its decider is…
--
--   **Swapping the state exchanges the two factors of a Born probability.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder Kronecker
--   variable {X A dA dB : Type*} [Fintype X] [Fintype A] [Fintype dA] [DecidableEq dA]
--
--   theorem MIPRE.bornProb_swapVec (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) (EB : Matrix dB dB ℂ) :
--       bornProb (swapVec ψ) EB EA = bornProb ψ EA EB
--   ```
--
--   **Formalization Note** `MIPRE.bornProb_swapVec` is declared in `MIPRE/Foundations/Swap.lean`, lines 35–59. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Swap.lean#L35-L59; blueprint lem:qld-combined-points

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Swap

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
variable {X A dA dB : Type*} [Fintype X] [Fintype A] [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
omit [DecidableEq dA] [DecidableEq dB]

theorem MIPRE.bornProb_swapVec (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) (EB : Matrix dB dB ℂ) :
    bornProb (swapVec ψ) EB EA = bornProb ψ EA EB := by sorry
