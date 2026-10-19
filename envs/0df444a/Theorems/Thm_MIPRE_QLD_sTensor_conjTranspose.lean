-- Prove2me | Theorems.Thm_MIPRE_QLD_sTensor_conjTranspose
-- name    : MIPRE.QLD.sTensor_conjTranspose
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:48:36.276407+00:00
-- url     : https://prove2.me/theorems/45042342-899b-4cd2-ba67-76b8b7a74910
-- title:
--   Adjoints are taken factorwise
-- statement:
--   A statement of the module `MIPRE.Background.QLD.SwapUnitary` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The swap unitary, and why two twirls force an EPR pair. Blueprint `lem:qld-swap`, the part of it that is **exact**, together with the elementary estimate that turns the exact part into the closeness statement. The appendix builds, out of the simultaneous pair measurement `S`, a *local unitary* `V = sum_{(g_X, g_Z)} S_{g_X,g_Z} (x) tau^X(cd g_Z) tau^Z(cd g_X)` and shows that conjugation by it carries each exact Pauli observable `wTilde` of `MIPRE/Background/QLD/ExactPauli.lean` to a *bare* Weyl operator on the ancilla, `V W~^e(u) V^dagger = Id (x) tau^W(e . u)`. Both statements are identities,…
--
--   Adjoints are taken factorwise.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.QLD
--   open Finset Matrix MIPRE MIPRE.Weyl
--   open scoped Kronecker ComplexOrder MatrixOrder
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
--   variable {n : Type*} [Fintype n] [DecidableEq n]
--   variable {G : Type*} [Fintype G] [DecidableEq G]
--   variable {dA : Type*} [Fintype dA] [DecidableEq dA]
--
--   theorem MIPRE.QLD.sTensor_conjTranspose {S : G × G → Matrix dA dA ℂ} (hS : IsPVM S)
--       (T : G × G → Matrix (n → F) (n → F) ℂ) :
--       (sTensor S T)ᴴ = sTensor S fun p => (T p)ᴴ
--   ```
--
--   **Formalization Note** `MIPRE.QLD.sTensor_conjTranspose` is declared in `MIPRE/Background/QLD/SwapUnitary.lean`, lines 101–107. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/SwapUnitary.lean#L101-L107; blueprint lem:qld-swap

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
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
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Background_QLD_ExactPauli
import Definitions.Def_MIPRE_Background_QLD_SwapUnitary

open MIPRE
open MIPRE.QLD
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]

theorem MIPRE.QLD.sTensor_conjTranspose {S : G × G → Matrix dA dA ℂ} (hS : IsPVM S)
    (T : G × G → Matrix (n → F) (n → F) ℂ) :
    (sTensor S T)ᴴ = sTensor S fun p => (T p)ᴴ := by sorry
