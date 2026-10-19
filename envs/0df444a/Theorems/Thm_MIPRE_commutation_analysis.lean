-- Prove2me | Theorems.Thm_MIPRE_commutation_analysis
-- name    : MIPRE.commutation_analysis
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:08:43.114915+00:00
-- url     : https://prove2.me/theorems/751a801d-e193-4734-b30f-031a1db10839
-- title:
--   The commutation analysis (lem:commutation-analysis)
-- statement:
--   A statement of the module `MIPRE.Foundations.Commutation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The commutation analysis. Blueprint `lem:commutation-analysis` (the paper's, in `games.tex`), and the two facts it runs on. It is the step that turns *consistency with a joint measurement on the other side* into *approximate commutation on one side*, and it is the only place in the Pauli appendix where projectivity of a measurement is genuinely used.
--
--   **The commutation analysis** (`lem:commutation-analysis`). Two POVMs on Alice's factor, each
--   cross-party close to the corresponding marginal of one **projective** measurement on Bob's,
--   commute on the state at `16 delta`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
--
--   theorem MIPRE.commutation_analysis {ψ : dA × dB → ℂ} {A : POVM B dA} {Cm : POVM C dA}
--       {P : B × C → Matrix dB dB ℂ} (hP : IsPVM P) {δ : ℝ}
--       (hA : ∑ b, snorm ψ ((aOp ((A.mats b).val) : Matrix (dA × dB) (dA × dB) ℂ)
--           - bOp (∑ c, P (b, c))) ^ 2 ≤ δ)
--       (hC : ∑ c, snorm ψ ((aOp ((Cm.mats c).val) : Matrix (dA × dB) (dA × dB) ℂ)
--           - bOp (∑ b, P (b, c))) ^ 2 ≤ δ) :
--       ∑ p : B × C, snorm ψ ((aOp ((A.mats p.1).val) : Matrix (dA × dB) (dA × dB) ℂ)
--             * aOp ((Cm.mats p.2).val)
--           - (aOp ((Cm.mats p.2).val) : Matrix (dA × dB) (dA × dB) ℂ)
--             * aOp ((A.mats p.1).val)) ^ 2 ≤ 16 * δ
--   ```
--
--   **Formalization Note** `MIPRE.commutation_analysis` is declared in `MIPRE/Foundations/Commutation.lean`, lines 582–607. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Commutation.lean#L582-L607; blueprint lem:commutation-analysis

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
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

theorem MIPRE.commutation_analysis {ψ : dA × dB → ℂ} {A : POVM B dA} {Cm : POVM C dA}
    {P : B × C → Matrix dB dB ℂ} (hP : IsPVM P) {δ : ℝ}
    (hA : ∑ b, snorm ψ ((aOp ((A.mats b).val) : Matrix (dA × dB) (dA × dB) ℂ)
        - bOp (∑ c, P (b, c))) ^ 2 ≤ δ)
    (hC : ∑ c, snorm ψ ((aOp ((Cm.mats c).val) : Matrix (dA × dB) (dA × dB) ℂ)
        - bOp (∑ b, P (b, c))) ^ 2 ≤ δ) :
    ∑ p : B × C, snorm ψ ((aOp ((A.mats p.1).val) : Matrix (dA × dB) (dA × dB) ℂ)
          * aOp ((Cm.mats p.2).val)
        - (aOp ((Cm.mats p.2).val) : Matrix (dA × dB) (dA × dB) ℂ)
          * aOp ((A.mats p.1).val)) ^ 2 ≤ 16 * δ := by sorry
