-- Prove2me | Theorems.Thm_MIPRE_povmValue_swapVec_of_symm
-- name    : MIPRE.povmValue_swapVec_of_symm
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:41.942089+00:00
-- url     : https://prove2.me/theorems/c3355265-20fd-4a5b-8748-dfeb45a61e67
-- title:
--   The value of a strategy for a symmetric game is unchanged by exchanging the players. Both halves of the hypothesis are needed, and both are properties of the *game*: the…
-- statement:
--   A statement of the module `MIPRE.Foundations.Swap` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Exchanging the two players. A game whose question distribution and decision predicate are both symmetric in the players is unchanged by exchanging them, and so is the value of a strategy once the state is swapped (`povmValue_swapVec_of_symm`). That is what turns a one-sided soundness statement --- one proved about Alice's measurements, with Bob's only as the other party --- into the statement about **Bob's**, with no second proof: apply it to `(MB, MA)` on `swapVec ψ`, and read the conclusion back through `norm_stateVecB`. The Pauli basis test is such a game: every rule of its decider is…
--
--   **The value of a strategy for a symmetric game is unchanged by exchanging the players.** Both
--   halves of the hypothesis are needed, and both are properties of the *game*: the question
--   distribution is symmetric, and the decider accepts a swapped question pair with the answers
--   swapped too.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder Kronecker
--   variable {X A dA dB : Type*} [Fintype X] [Fintype A] [Fintype dA] [DecidableEq dA]
--
--   theorem MIPRE.povmValue_swapVec_of_symm {G : Game X X A A} (ψ : dA × dB → ℂ)
--       (MA : X → POVM A dA) (MB : X → POVM A dB)
--       (hμ : ∀ x y, G.μ x y = G.μ y x) (hD : ∀ x y a b, G.D x y a b = G.D y x b a) :
--       povmValue G (swapVec ψ) MB MA = povmValue G ψ MA MB
--   ```
--
--   **Formalization Note** `MIPRE.povmValue_swapVec_of_symm` is declared in `MIPRE/Foundations/Swap.lean`, lines 64–90. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Swap.lean#L64-L90; blueprint lem:qld-combined-points

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

theorem MIPRE.povmValue_swapVec_of_symm {G : Game X X A A} (ψ : dA × dB → ℂ)
    (MA : X → POVM A dA) (MB : X → POVM A dB)
    (hμ : ∀ x y, G.μ x y = G.μ y x) (hD : ∀ x y a b, G.D x y a b = G.D y x b a) :
    povmValue G (swapVec ψ) MB MA = povmValue G ψ MA MB := by sorry
