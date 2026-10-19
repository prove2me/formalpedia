-- Prove2me | Theorems.Thm_MIPRE_sum_collisionTerm_le
-- name    : MIPRE.sum_collisionTerm_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:43:15.613993+00:00
-- url     : https://prove2.me/theorems/ee4321f4-79b1-48e6-9b39-5ba666525639
-- title:
--   The collision term is at most the average collision probability. The question is a pair: a part z that all the measurements see, and a probe y, uniform and independent of…
-- statement:
--   A statement of the module `MIPRE.Foundations.Pasting` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Pasting two measurements into one. The blueprint's missing piece for `lem:qld-pairs-of-lines`: NW19's Fact 4.35, the paper's `lem:pasting-updated`. One party holds a *joint* projective measurement `A_{a,b}`; the other holds two projective measurements `G_1` and `G_2` whose coarse-grainings along evaluation maps agree with `A`'s two marginals. The conclusion is that `A` agrees with the **sandwich** `J_{g_1, g_2} = G_2^{g_2} G_1^{g_1} G_2^{g_2}`, coarse-grained by evaluating both outcomes. Two facts beyond the sandwich chain of `MIPRE/Foundations/Sandwich.lean` are needed, and they are proved…
--
--   **The collision term is at most the average collision probability.** The question is a pair: a
--   part `z` that all the measurements see, and a probe `y`, uniform and independent of `z`, that only
--   the outcome map sees. The Born probabilities do not depend on `y`, so the probe average acts on the
--   indicator alone; what is left is a POVM's total mass, which is one.
--
--   The collision probability is allowed to depend on `z`, and the conclusion is its average. The
--   consumer needs that: for a degenerate line the outcome map separates nothing, and what makes the
--   average small is that such lines are rare rather than that the bound holds everywhere.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder Kronecker
--   variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
--   variable {Z Y R1 R2 K : Type*} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
--
--   theorem MIPRE.sum_collisionTerm_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) {ν : Z → ℝ}
--       (hν0 : ∀ z, 0 ≤ ν z)
--       {R : Z → R1 → Matrix dB dB ℂ} {G : Z → K → Matrix dB dB ℂ} {Ga : Z → K → Matrix dA dA ℂ}
--       (hR : ∀ z, IsPVM (R z)) (hG : ∀ z, IsPVM (G z)) (hGa : ∀ z, IsPVM (Ga z))
--       (e : Z → Y → K → R2) {εz : Z → ℝ} (hε : ∀ z, 0 ≤ εz z)
--       (hsep : ∀ (z : Z) (g g' : K), g' ≠ g →
--         ((univ.filter fun y : Y => e z y g' = e z y g).card : ℝ) ≤ εz z * (Fintype.card Y : ℝ)) :
--       ∑ i : Z × Y, (ν i.1 * (Fintype.card Y : ℝ)⁻¹)
--           * collisionTerm ψ (R i.1) (G i.1) (Ga i.1) (e i.1 i.2) ≤ ∑ z : Z, ν z * εz z
--   ```
--
--   **Formalization Note** `MIPRE.sum_collisionTerm_le` is declared in `MIPRE/Foundations/Pasting.lean`, lines 1294–1375. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pasting.lean#L1294-L1375; blueprint lem:pasting-updated

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
variable {Z Y R1 R2 K : Type*} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]

theorem MIPRE.sum_collisionTerm_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) {ν : Z → ℝ}
    (hν0 : ∀ z, 0 ≤ ν z)
    {R : Z → R1 → Matrix dB dB ℂ} {G : Z → K → Matrix dB dB ℂ} {Ga : Z → K → Matrix dA dA ℂ}
    (hR : ∀ z, IsPVM (R z)) (hG : ∀ z, IsPVM (G z)) (hGa : ∀ z, IsPVM (Ga z))
    (e : Z → Y → K → R2) {εz : Z → ℝ} (hε : ∀ z, 0 ≤ εz z)
    (hsep : ∀ (z : Z) (g g' : K), g' ≠ g →
      ((univ.filter fun y : Y => e z y g' = e z y g).card : ℝ) ≤ εz z * (Fintype.card Y : ℝ)) :
    ∑ i : Z × Y, (ν i.1 * (Fintype.card Y : ℝ)⁻¹)
        * collisionTerm ψ (R i.1) (G i.1) (Ga i.1) (e i.1 i.2) ≤ ∑ z : Z, ν z * εz z := by sorry
