-- Prove2me | Theorems.Thm_MIPRE_Introspection_unitaryTwirl_comp
-- name    : MIPRE.Introspection.unitaryTwirl_comp
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:09:20.746197+00:00
-- url     : https://prove2.me/theorems/52d57476-471d-41ab-9f49-8ca230cb13d5
-- title:
--   Successive twirls equal the twirl by the independently sampled product
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.ComposedTwirl` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Composed twirling from two commutator estimates
--
--   Successive twirls equal the twirl by the independently sampled product.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix
--   variable {dA dB I J A : Type*} [Fintype dA] [DecidableEq dA]
--
--   theorem MIPRE.Introspection.unitaryTwirl_comp (μ : I → ℝ) (ν : J → ℝ)
--       (U : I → Matrix dA dA ℂ) (V : J → Matrix dA dA ℂ) (M : Matrix dA dA ℂ) :
--       unitaryTwirl ν V (unitaryTwirl μ U M) =
--         unitaryTwirl (fun p : I × J => μ p.1 * ν p.2) (fun p => V p.2 * U p.1) M
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.unitaryTwirl_comp` is declared in `MIPRE/Foundations/Introspection/ComposedTwirl.lean`, lines 19–35. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ComposedTwirl.lean#L19-L35; blueprint lem:pauli-two-sided-commutation

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
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance

open MIPRE
open MIPRE.Introspection
open Finset Matrix
variable {dA dB I J A : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB] [Fintype I] [Fintype J] [Fintype A]

theorem MIPRE.Introspection.unitaryTwirl_comp (μ : I → ℝ) (ν : J → ℝ)
    (U : I → Matrix dA dA ℂ) (V : J → Matrix dA dA ℂ) (M : Matrix dA dA ℂ) :
    unitaryTwirl ν V (unitaryTwirl μ U M) =
      unitaryTwirl (fun p : I × J => μ p.1 * ν p.2) (fun p => V p.2 * U p.1) M := by sorry
