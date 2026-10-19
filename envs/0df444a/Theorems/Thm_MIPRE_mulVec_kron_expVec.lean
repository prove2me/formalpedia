-- Prove2me | Theorems.Thm_MIPRE_mulVec_kron_expVec
-- name    : MIPRE.mulVec_kron_expVec
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:52:39.123261+00:00
-- url     : https://prove2.me/theorems/97c53613-a737-4764-802d-76c126e2d0ab
-- title:
--   An operator of product form acts on the expanded state factor by factor
-- statement:
--   A statement of the module `MIPRE.Foundations.Expanded` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The expanded state, and an inert ancilla. The expansion stage of the Pauli appendix (`sec:expanding`) adjoins a maximally entangled pair of ancilla registers to each player and then **re-bipartitions**: Alice's party becomes her own register together with her half of the ancilla, and Bob's becomes his register together with the *other* half. This file is that construction, for an arbitrary ancilla state.
--
--   **An operator of product form acts on the expanded state factor by factor.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped Kronecker ComplexOrder MatrixOrder
--   variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
--
--   theorem MIPRE.mulVec_kron_expVec (ψ : dA × dB → ℂ) (e : anc × anc' → ℂ) (M : Matrix dA dA ℂ)
--       (N : Matrix anc anc ℂ) :
--       (((M ⊗ₖ N) ⊗ₖ (1 : Matrix (dB × anc') (dB × anc') ℂ)) *ᵥ expVec ψ e)
--         = expVec ((M ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ) ((N ⊗ₖ (1 : Matrix anc' anc' ℂ)) *ᵥ e)
--   ```
--
--   **Formalization Note** `MIPRE.mulVec_kron_expVec` is declared in `MIPRE/Foundations/Expanded.lean`, lines 97–120. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Expanded.lean#L97-L120; blueprint def:expanded-state

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
import Definitions.Def_MIPRE_Foundations_Expanded

open MIPRE
open Finset Matrix
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB anc anc' : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  [Fintype anc] [DecidableEq anc] [Fintype anc'] [DecidableEq anc']

theorem MIPRE.mulVec_kron_expVec (ψ : dA × dB → ℂ) (e : anc × anc' → ℂ) (M : Matrix dA dA ℂ)
    (N : Matrix anc anc ℂ) :
    (((M ⊗ₖ N) ⊗ₖ (1 : Matrix (dB × anc') (dB × anc') ℂ)) *ᵥ expVec ψ e)
      = expVec ((M ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ) ((N ⊗ₖ (1 : Matrix anc' anc' ℂ)) *ᵥ e) := by sorry
