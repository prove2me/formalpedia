-- Prove2me | Theorems.Thm_MIPRE_Introspection_retained_block_le_completion
-- name    : MIPRE.Introspection.retained_block_le_completion
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:07:12.483103+00:00
-- url     : https://prove2.me/theorems/fec67a23-6b97-4873-9cf3-a526361f6796
-- title:
--   The matching block is positive and dominated by the controlled marginal POVM
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.BlockRetention` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Completing the matching blocks of a twirled measurement
--
--   The matching block is positive and dominated by the controlled marginal POVM.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix Classical
--   open scoped Kronecker ComplexOrder MatrixOrder
--   variable {V H Y A : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
--
--   theorem MIPRE.Introspection.retained_block_le_completion (P : Y → Matrix V V ℂ) (hP : IsPVM P)
--       (Q : Y → POVM (Y × A) H) (p : Y × A) :
--       P p.1 ⊗ₖ ((Q p.1).mats p).val ≤
--         ((controlledPOVM P hP (fun y => (Q y).map Prod.snd)).mats p).val
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.retained_block_le_completion` is declared in `MIPRE/Foundations/Introspection/BlockRetention.lean`, lines 63–78. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/BlockRetention.lean#L63-L78; blueprint lem:pauli-mixing-coordinates

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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention

open MIPRE
open MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
variable {V H Y A : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]

theorem MIPRE.Introspection.retained_block_le_completion (P : Y → Matrix V V ℂ) (hP : IsPVM P)
    (Q : Y → POVM (Y × A) H) (p : Y × A) :
    P p.1 ⊗ₖ ((Q p.1).mats p).val ≤
      ((controlledPOVM P hP (fun y => (Q y).map Prod.snd)).mats p).val := by sorry
