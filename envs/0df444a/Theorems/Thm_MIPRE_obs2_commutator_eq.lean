-- Prove2me | Theorems.Thm_MIPRE_obs2_commutator_eq
-- name    : MIPRE.obs2_commutator_eq
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:08:30.039011+00:00
-- url     : https://prove2.me/theorems/ef167977-f5eb-4ab0-92a4-dd8ba807511a
-- title:
--   Lemma obs2_commutator_eq of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Commutation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The commutation analysis. Blueprint `lem:commutation-analysis` (the paper's, in `games.tex`), and the two facts it runs on. It is the step that turns *consistency with a joint measurement on the other side* into *approximate commutation on one side*, and it is the only place in the Pauli appendix where projectivity of a measurement is genuinely used.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
--
--   theorem MIPRE.obs2_commutator_eq {d : Type*} [Fintype d] [DecidableEq d]
--       (A : POVM (ZMod 2) d) (Cm : POVM (ZMod 2) d) :
--       obs2 A * obs2 Cm - obs2 Cm * obs2 A
--         = (4 : ℂ) • (((A.mats 1).val) * ((Cm.mats 1).val)
--           - ((Cm.mats 1).val) * ((A.mats 1).val))
--   ```
--
--   **Formalization Note** `MIPRE.obs2_commutator_eq` is declared in `MIPRE/Foundations/Commutation.lean`, lines 629–646. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Commutation.lean#L629-L646; blueprint lem:commutation-analysis

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

theorem MIPRE.obs2_commutator_eq {d : Type*} [Fintype d] [DecidableEq d]
    (A : POVM (ZMod 2) d) (Cm : POVM (ZMod 2) d) :
    obs2 A * obs2 Cm - obs2 Cm * obs2 A
      = (4 : ℂ) • (((A.mats 1).val) * ((Cm.mats 1).val)
        - ((Cm.mats 1).val) * ((A.mats 1).val)) := by sorry
