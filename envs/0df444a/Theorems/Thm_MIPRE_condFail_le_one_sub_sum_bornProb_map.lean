-- Prove2me | Theorems.Thm_MIPRE_condFail_le_one_sub_sum_bornProb_map
-- name    : MIPRE.condFail_le_one_sub_sum_bornProb_map
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:42:01.196377+00:00
-- url     : https://prove2.me/theorems/7b87677d-ddc0-4273-b2fd-34caafca212c
-- title:
--   Agreement on the support implies acceptance bounds the conditional failure by the disagreement of the relabelled POVMs. Only outcomes both parties can produce are asked to be…
-- statement:
--   A statement of the module `MIPRE.Foundations.POVMMix` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Mixtures and extensions of POVMs, and the agreement triangle. Three constructions on bundled POVMs that the padded strategy of the Pauli basis test's stage 4 needs, and one inequality. * `POVM.aOp` extends a POVM on `d` by the identity to `d × E`; `POVM.dirac a₀` answers `a₀` with certainty; `POVM.mix w Q` is a convex combination of POVMs with the same outcomes. A strategy that must be a *function of the question* while the analysis controls it *sample by sample* is a mixture over the samples producing the question, and the Born rule's linearity (`bornProb_mix_left`, `bornProb_mix_right`)…
--
--   **Agreement on the support implies acceptance bounds the conditional failure by the
--   disagreement of the relabelled POVMs.** Only outcomes both parties can produce are asked to be
--   accepted, which is what a strategy answering every question in its own format needs.
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
--   theorem MIPRE.condFail_le_one_sub_sum_bornProb_map {G : Game X Y A B} {MA : X → POVM A dA}
--       {MB : Y → POVM B dB} (f : A → C) (g : B → C)
--       (hD : ∀ a b, ((MA x).mats a).val ≠ 0 → ((MB y).mats b).val ≠ 0 → f a = g b →
--         G.D x y a b = true) :
--       condFail G ψ MA MB x y
--         ≤ 1 - ∑ c, bornProb ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val)
--   ```
--
--   **Formalization Note** `MIPRE.condFail_le_one_sub_sum_bornProb_map` is declared in `MIPRE/Foundations/POVMMix.lean`, lines 306–331. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/POVMMix.lean#L306-L331; blueprint lem:qld-global-setup

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

theorem MIPRE.condFail_le_one_sub_sum_bornProb_map {G : Game X Y A B} {MA : X → POVM A dA}
    {MB : Y → POVM B dB} (f : A → C) (g : B → C)
    (hD : ∀ a b, ((MA x).mats a).val ≠ 0 → ((MB y).mats b).val ≠ 0 → f a = g b →
      G.D x y a b = true) :
    condFail G ψ MA MB x y
      ≤ 1 - ∑ c, bornProb ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val) := by sorry
