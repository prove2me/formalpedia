-- Prove2me | Theorems.Thm_MIPRE_QLD_norm_sub_normalize_sq_le
-- name    : MIPRE.QLD.norm_sub_normalize_sq_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:52:40.682993+00:00
-- url     : https://prove2.me/theorems/4f8c2f14-cc34-4faa-a1c6-60234c98e338
-- title:
--   A state with large weight on a projector is close to its normalized projection. The appendix's extraction of the auxiliary state: with x = P theta for a projector P, the…
-- statement:
--   A statement of the module `MIPRE.Background.QLD.SwapUnitary` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The swap unitary, and why two twirls force an EPR pair. Blueprint `lem:qld-swap`, the part of it that is **exact**, together with the elementary estimate that turns the exact part into the closeness statement. The appendix builds, out of the simultaneous pair measurement `S`, a *local unitary* `V = sum_{(g_X, g_Z)} S_{g_X,g_Z} (x) tau^X(cd g_Z) tau^Z(cd g_X)` and shows that conjugation by it carries each exact Pauli observable `wTilde` of `MIPRE/Background/QLD/ExactPauli.lean` to a *bare* Weyl operator on the ancilla, `V W~^e(u) V^dagger = Id (x) tau^W(e . u)`. Both statements are identities,…
--
--   **A state with large weight on a projector is close to its normalized projection.** The
--   appendix's extraction of the auxiliary state: with `x = P theta` for a projector `P`, the
--   hypothesis `hx` is `<theta, P theta> = ||P theta||^2`, and the conclusion bounds the squared
--   distance from `theta` to the unit vector along `x`.
--
--   This is where the paper's `sqrt` enters, and the reason `lem:qld-swap`'s error is `delta_S^{1/4}`
--   and not `delta_S^{1/2}`: the overlap is the square root of the weight, and the squared distance is
--   twice its deficit.
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
--   variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
--
--   theorem MIPRE.QLD.norm_sub_normalize_sq_le {θ x : E} {η : ℝ} (hθ : ‖θ‖ = 1)
--       (hx : ‖x‖ ^ 2 = (inner ℂ θ x : ℂ).re) (hlt : η < 1)
--       (hlow : 1 - η ≤ (inner ℂ θ x : ℂ).re) :
--       ‖θ - ((‖x‖⁻¹ : ℝ) : ℂ) • x‖ ^ 2 ≤ 2 - 2 * Real.sqrt (1 - η)
--   ```
--
--   **Formalization Note** `MIPRE.QLD.norm_sub_normalize_sq_le` is declared in `MIPRE/Background/QLD/SwapUnitary.lean`, lines 406–440. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/SwapUnitary.lean#L406-L440; blueprint lem:qld-swap

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem MIPRE.QLD.norm_sub_normalize_sq_le {θ x : E} {η : ℝ} (hθ : ‖θ‖ = 1)
    (hx : ‖x‖ ^ 2 = (inner ℂ θ x : ℂ).re) (hlt : η < 1)
    (hlow : 1 - η ≤ (inner ℂ θ x : ℂ).re) :
    ‖θ - ((‖x‖⁻¹ : ℝ) : ℂ) • x‖ ^ 2 ≤ 2 - 2 * Real.sqrt (1 - η) := by sorry
