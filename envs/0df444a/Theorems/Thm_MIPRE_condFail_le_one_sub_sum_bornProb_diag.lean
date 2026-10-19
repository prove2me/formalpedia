-- Prove2me | Theorems.Thm_MIPRE_condFail_le_one_sub_sum_bornProb_diag
-- name    : MIPRE.condFail_le_one_sub_sum_bornProb_diag
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:42:06.200247+00:00
-- url     : https://prove2.me/theorems/17032237-965d-4b5c-9247-b0949fd2dc6e
-- title:
--   The same with both parties' outcomes read as they are: acceptance of every diagonal pair on the support bounds the conditional failure by the diagonal disagreement
-- statement:
--   A statement of the module `MIPRE.Foundations.POVMMix` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Mixtures and extensions of POVMs, and the agreement triangle. Three constructions on bundled POVMs that the padded strategy of the Pauli basis test's stage 4 needs, and one inequality. * `POVM.aOp` extends a POVM on `d` by the identity to `d × E`; `POVM.dirac a₀` answers `a₀` with certainty; `POVM.mix w Q` is a convex combination of POVMs with the same outcomes. A strategy that must be a *function of the question* while the analysis controls it *sample by sample* is a mixture over the samples producing the question, and the Born rule's linearity (`bornProb_mix_left`, `bornProb_mix_right`)…
--
--   The same with both parties' outcomes read as they are: acceptance of every diagonal pair
--   on the support bounds the conditional failure by the diagonal disagreement.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix Kronecker
--   open scoped ComplexOrder MatrixOrder
--   variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
--   variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
--
--   theorem MIPRE.condFail_le_one_sub_sum_bornProb_diag {G : Game X Y A A} {MA : X → POVM A dA}
--       {MB : Y → POVM A dB}
--       (hD : ∀ a, ((MA x).mats a).val ≠ 0 → ((MB y).mats a).val ≠ 0 → G.D x y a a = true) :
--       condFail G ψ MA MB x y
--         ≤ 1 - ∑ a, bornProb ψ (((MA x).mats a).val) (((MB y).mats a).val)
--   ```
--
--   **Formalization Note** `MIPRE.condFail_le_one_sub_sum_bornProb_diag` is declared in `MIPRE/Foundations/POVMMix.lean`, lines 333–356. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/POVMMix.lean#L333-L356; blueprint lem:qld-global-setup

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
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_POVMMix_B

open MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq C] {ψ : dA × dB → ℂ} {x : X} {y : Y}

theorem MIPRE.condFail_le_one_sub_sum_bornProb_diag {G : Game X Y A A} {MA : X → POVM A dA}
    {MB : Y → POVM A dB}
    (hD : ∀ a, ((MA x).mats a).val ≠ 0 → ((MB y).mats a).val ≠ 0 → G.D x y a a = true) :
    condFail G ψ MA MB x y
      ≤ 1 - ∑ a, bornProb ψ (((MA x).mats a).val) (((MB y).mats a).val) := by sorry
