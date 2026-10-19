-- Prove2me | Theorems.Thm_MIPRE_one_sub_sum_bornProb_pasteJ_le
-- name    : MIPRE.one_sub_sum_bornProb_pasteJ_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:43:13.719873+00:00
-- url     : https://prove2.me/theorems/196e2f66-5176-43c6-aca6-b16dafec9971
-- title:
--   The pasting lemma, k = 2 (NW19's Fact 4.35, the paper's lem:pasting-updated), in Born probability form: Alice's joint measurement agrees with the pasted sandwich up to…
-- statement:
--   A statement of the module `MIPRE.Foundations.Pasting` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Pasting two measurements into one. The blueprint's missing piece for `lem:qld-pairs-of-lines`: NW19's Fact 4.35, the paper's `lem:pasting-updated`. One party holds a *joint* projective measurement `A_{a,b}`; the other holds two projective measurements `G_1` and `G_2` whose coarse-grainings along evaluation maps agree with `A`'s two marginals. The conclusion is that `A` agrees with the **sandwich** `J_{g_1, g_2} = G_2^{g_2} G_1^{g_1} G_2^{g_2}`, coarse-grained by evaluating both outcomes. Two facts beyond the sandwich chain of `MIPRE/Foundations/Sandwich.lean` are needed, and they are proved…
--
--   **The pasting lemma, `k = 2`** (NW19's Fact 4.35, the paper's `lem:pasting-updated`), in Born
--   probability form: Alice's joint measurement agrees with the pasted sandwich up to
--   `delta/2 + sqrt(delta/2) + sqrt(32 delta + 4 sqrt(eta) + 2 eps)`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder Kronecker
--   variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
--   variable {ι R1 R2 K : Type*} [Fintype ι] [Fintype R1] [DecidableEq R1] [Fintype R2]
--
--   theorem MIPRE.one_sub_sum_bornProb_pasteJ_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
--       {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
--       {A : ι → R1 × R2 → Matrix dA dA ℂ} {R : ι → R1 → Matrix dB dB ℂ}
--       {G : ι → K → Matrix dB dB ℂ} {Ga : ι → K → Matrix dA dA ℂ} (e : ι → K → R2)
--       (hA : ∀ i, IsPVM (A i)) (hR : ∀ i, IsPVM (R i)) (hG : ∀ i, IsPVM (G i))
--       (hGa : ∀ i, IsPVM (Ga i)) {δ η ε : ℝ}
--       (hP1 : ∑ i, w i * ∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a) ≤ δ)
--       (hP2 : ∑ i, w i * ∑ b : R2,
--         xSqNorm ψ (∑ a : R1, A i (a, b)) (fibSum (G i) (e i) b) ≤ δ)
--       (hP4 : ∑ i, w i * ∑ g : K, xSqNorm ψ (Ga i g) (G i g) ≤ η)
--       (hcoll : ∑ i, w i * collisionTerm ψ (R i) (G i) (Ga i) (e i) ≤ ε) :
--       1 - ∑ i, w i * ∑ p : R1 × R2, bornProb ψ (A i p) (pasteJ (R i) (G i) (e i) p)
--         ≤ δ / 2 + Real.sqrt (δ / 2) + Real.sqrt (32 * δ + 4 * Real.sqrt η + 2 * ε)
--   ```
--
--   **Formalization Note** `MIPRE.one_sub_sum_bornProb_pasteJ_le` is declared in `MIPRE/Foundations/Pasting.lean`, lines 1193–1281. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pasting.lean#L1193-L1281; blueprint lem:pasting-updated

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
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {ι R1 R2 K : Type*} [Fintype ι] [Fintype R1] [DecidableEq R1] [Fintype R2]
  [DecidableEq R2] [Fintype K] [DecidableEq K]

theorem MIPRE.one_sub_sum_bornProb_pasteJ_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    {A : ι → R1 × R2 → Matrix dA dA ℂ} {R : ι → R1 → Matrix dB dB ℂ}
    {G : ι → K → Matrix dB dB ℂ} {Ga : ι → K → Matrix dA dA ℂ} (e : ι → K → R2)
    (hA : ∀ i, IsPVM (A i)) (hR : ∀ i, IsPVM (R i)) (hG : ∀ i, IsPVM (G i))
    (hGa : ∀ i, IsPVM (Ga i)) {δ η ε : ℝ}
    (hP1 : ∑ i, w i * ∑ a : R1, xSqNorm ψ (∑ b : R2, A i (a, b)) (R i a) ≤ δ)
    (hP2 : ∑ i, w i * ∑ b : R2,
      xSqNorm ψ (∑ a : R1, A i (a, b)) (fibSum (G i) (e i) b) ≤ δ)
    (hP4 : ∑ i, w i * ∑ g : K, xSqNorm ψ (Ga i g) (G i g) ≤ η)
    (hcoll : ∑ i, w i * collisionTerm ψ (R i) (G i) (Ga i) (e i) ≤ ε) :
    1 - ∑ i, w i * ∑ p : R1 × R2, bornProb ψ (A i p) (pasteJ (R i) (G i) (e i) p)
      ≤ δ / 2 + Real.sqrt (δ / 2) + Real.sqrt (32 * δ + 4 * Real.sqrt η + 2 * ε) := by sorry
