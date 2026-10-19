-- Prove2me | Theorems.Thm_MIPRE_QLD_uOf_conj_wX
-- name    : MIPRE.QLD.uOf_conj_wX
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:50:15.297332+00:00
-- url     : https://prove2.me/theorems/27e562d9-b0ef-42ca-ab3d-134ab4a61513
-- title:
--   (tau^X(x) tau^Z(z)) tau^X(a) (tau^X(x) tau^Z(z))^dagger = (-1)^{tr(a
-- statement:
--   A statement of the module `MIPRE.Background.QLD.SwapUnitary` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The swap unitary, and why two twirls force an EPR pair. Blueprint `lem:qld-swap`, the part of it that is **exact**, together with the elementary estimate that turns the exact part into the closeness statement. The appendix builds, out of the simultaneous pair measurement `S`, a *local unitary* `V = sum_{(g_X, g_Z)} S_{g_X,g_Z} (x) tau^X(cd g_Z) tau^Z(cd g_X)` and shows that conjugation by it carries each exact Pauli observable `wTilde` of `MIPRE/Background/QLD/ExactPauli.lean` to a *bare* Weyl operator on the ancilla, `V W~^e(u) V^dagger = Id (x) tau^W(e . u)`. Both statements are identities,…
--
--   `(tau^X(x) tau^Z(z)) tau^X(a) (tau^X(x) tau^Z(z))^dagger = (-1)^{tr(a . z)} tau^X(a)`.
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
--   variable {S : G × G → Matrix dA dA ℂ} {cd : G → (n → F)}
--
--   theorem MIPRE.QLD.uOf_conj_wX (cd : G → (n → F)) (p : G × G) (a : n → F) :
--       uOf cd p * wX a * (uOf cd p)ᴴ = sgn (trDot a (cd p.1)) • wX a
--   ```
--
--   **Formalization Note** `MIPRE.QLD.uOf_conj_wX` is declared in `MIPRE/Background/QLD/SwapUnitary.lean`, lines 168–182. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/SwapUnitary.lean#L168-L182; blueprint lem:qld-swap

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
variable {S : G × G → Matrix dA dA ℂ} {cd : G → (n → F)}

theorem MIPRE.QLD.uOf_conj_wX (cd : G → (n → F)) (p : G × G) (a : n → F) :
    uOf cd p * wX a * (uOf cd p)ᴴ = sgn (trDot a (cd p.1)) • wX a := by sorry
