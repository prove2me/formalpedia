-- Prove2me | Theorems.Thm_MIPRE_commutation_analysis_abstract
-- name    : MIPRE.commutation_analysis_abstract
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:08:19.400155+00:00
-- url     : https://prove2.me/theorems/c6731f32-0562-4d3e-a301-dfcae64b5c33
-- title:
--   The commutation analysis, in one algebra. alpha and gamma are the two families that are to commute; betaB, betaC are what they are respectively close to, and betaBC…
-- statement:
--   A statement of the module `MIPRE.Foundations.Commutation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The commutation analysis. Blueprint `lem:commutation-analysis` (the paper's, in `games.tex`), and the two facts it runs on. It is the step that turns *consistency with a joint measurement on the other side* into *approximate commutation on one side*, and it is the only place in the Pauli appendix where projectivity of a measurement is genuinely used.
--
--   **The commutation analysis, in one algebra.** `alpha` and `gamma` are the two families that
--   are to commute; `betaB`, `betaC` are what they are respectively close to, and `betaBC` is the
--   joint operator both products reach.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {N : Type*} [Fintype N] [DecidableEq N] {B C : Type*} [Fintype B] [Fintype C]
--
--   theorem MIPRE.commutation_analysis_abstract (v : N → ℂ)
--       (alpha : B → Matrix N N ℂ) (gamma : C → Matrix N N ℂ)
--       (betaB : B → Matrix N N ℂ) (betaC : C → Matrix N N ℂ)
--       (betaBC : B × C → Matrix N N ℂ)
--       (halpha : ∑ b, (alpha b)ᴴ * alpha b ≤ (1 : Matrix N N ℂ))
--       (hgamma : ∑ c, (gamma c)ᴴ * gamma c ≤ (1 : Matrix N N ℂ))
--       (hbetaB : ∑ b, (betaB b)ᴴ * betaB b ≤ (1 : Matrix N N ℂ))
--       (hbetaC : ∑ c, (betaC c)ᴴ * betaC c ≤ (1 : Matrix N N ℂ))
--       (hcomm : ∀ b c, alpha b * betaC c = betaC c * alpha b)
--       (hcomm' : ∀ b c, gamma c * betaB b = betaB b * gamma c)
--       (hmul : ∀ b c, betaC c * betaB b = betaBC (b, c))
--       (hmul' : ∀ b c, betaB b * betaC c = betaBC (b, c))
--       (hA : ∑ b, snorm v (alpha b - betaB b) ^ 2 ≤ δ)
--       (hC : ∑ c, snorm v (gamma c - betaC c) ^ 2 ≤ δ) :
--       ∑ p : B × C, snorm v (alpha p.1 * gamma p.2 - gamma p.2 * alpha p.1) ^ 2 ≤ 16 * δ
--   ```
--
--   **Formalization Note** `MIPRE.commutation_analysis_abstract` is declared in `MIPRE/Foundations/Commutation.lean`, lines 520–571. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Commutation.lean#L520-L571; blueprint lem:commutation-analysis

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N] {B C : Type*} [Fintype B] [Fintype C]
  {v : N → ℂ} {δ : ℝ}

theorem MIPRE.commutation_analysis_abstract (v : N → ℂ)
    (alpha : B → Matrix N N ℂ) (gamma : C → Matrix N N ℂ)
    (betaB : B → Matrix N N ℂ) (betaC : C → Matrix N N ℂ)
    (betaBC : B × C → Matrix N N ℂ)
    (halpha : ∑ b, (alpha b)ᴴ * alpha b ≤ (1 : Matrix N N ℂ))
    (hgamma : ∑ c, (gamma c)ᴴ * gamma c ≤ (1 : Matrix N N ℂ))
    (hbetaB : ∑ b, (betaB b)ᴴ * betaB b ≤ (1 : Matrix N N ℂ))
    (hbetaC : ∑ c, (betaC c)ᴴ * betaC c ≤ (1 : Matrix N N ℂ))
    (hcomm : ∀ b c, alpha b * betaC c = betaC c * alpha b)
    (hcomm' : ∀ b c, gamma c * betaB b = betaB b * gamma c)
    (hmul : ∀ b c, betaC c * betaB b = betaBC (b, c))
    (hmul' : ∀ b c, betaB b * betaC c = betaBC (b, c))
    (hA : ∑ b, snorm v (alpha b - betaB b) ^ 2 ≤ δ)
    (hC : ∑ c, snorm v (gamma c - betaC c) ^ 2 ≤ δ) :
    ∑ p : B × C, snorm v (alpha p.1 * gamma p.2 - gamma p.2 * alpha p.1) ^ 2 ≤ 16 * δ := by sorry
