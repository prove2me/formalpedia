-- Prove2me | Theorems.Thm_MIPRE_qform_sum_ge_of_close
-- name    : MIPRE.qform_sum_ge_of_close
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:42:31.347969+00:00
-- url     : https://prove2.me/theorems/e761a038-fb30-4d2e-aacd-196861d300a7
-- title:
--   NW19's Fact 4.31. A family of positive operators summing to at most the identity, which is delta-close to a projective measurement on a state, carries all but 2…
-- statement:
--   A statement of the module `MIPRE.Foundations.Pasting` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Pasting two measurements into one. The blueprint's missing piece for `lem:qld-pairs-of-lines`: NW19's Fact 4.35, the paper's `lem:pasting-updated`. One party holds a *joint* projective measurement `A_{a,b}`; the other holds two projective measurements `G_1` and `G_2` whose coarse-grainings along evaluation maps agree with `A`'s two marginals. The conclusion is that `A` agrees with the **sandwich** `J_{g_1, g_2} = G_2^{g_2} G_1^{g_1} G_2^{g_2}`, coarse-grained by evaluating both outcomes. Two facts beyond the sandwich chain of `MIPRE/Foundations/Sandwich.lean` are needed, and they are proved…
--
--   **NW19's Fact 4.31.** A family of positive operators summing to at most the identity, which is
--   `delta`-close to a projective measurement on a state, carries all but `2 sqrt(delta)` of the mass.
--   Two Cauchy--Schwarz steps against the same deviation: one moves from `1` to `sum <M_c P_c>`, the
--   other from there to `sum <P_c^2>`, and `P_c^2 <= P_c`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder Kronecker
--   variable {N : Type*} [Fintype N] [DecidableEq N] {C : Type*} [Fintype C] [DecidableEq C]
--
--   theorem MIPRE.qform_sum_ge_of_close {v : N → ℂ} (hv : ‖evec v‖ = 1) {M P : C → Matrix N N ℂ}
--       (hM : IsPVM M) (hP0 : ∀ c, (0 : Matrix N N ℂ) ≤ P c)
--       (hPsum : ∑ c, P c ≤ (1 : Matrix N N ℂ))
--       {δ : ℝ} (hclose : ∑ c, snorm v (M c - P c) ^ 2 ≤ δ) :
--       1 - 2 * Real.sqrt δ ≤ ∑ c, qform v (P c)
--   ```
--
--   **Formalization Note** `MIPRE.qform_sum_ge_of_close` is declared in `MIPRE/Foundations/Pasting.lean`, lines 84–149. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pasting.lean#L84-L149

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
import Definitions.Def_MIPRE_Foundations_Pasting

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N] {C : Type*} [Fintype C] [DecidableEq C]

theorem MIPRE.qform_sum_ge_of_close {v : N → ℂ} (hv : ‖evec v‖ = 1) {M P : C → Matrix N N ℂ}
    (hM : IsPVM M) (hP0 : ∀ c, (0 : Matrix N N ℂ) ≤ P c)
    (hPsum : ∑ c, P c ≤ (1 : Matrix N N ℂ))
    {δ : ℝ} (hclose : ∑ c, snorm v (M c - P c) ^ 2 ≤ δ) :
    1 - 2 * Real.sqrt δ ≤ ∑ c, qform v (P c) := by sorry
