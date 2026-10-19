-- Prove2me | Theorems.Thm_MIPRE_QLD_PauliCL_pullbackStrategy_value
-- name    : MIPRE.QLD.PauliCL.pullbackStrategy_value
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:06:25.30298+00:00
-- url     : https://prove2.me/theorems/87757f6e-e97c-4dd8-9e5a-cc467c41a03a
-- title:
--   Lemma pullbackStrategy_value of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Background.QLD.CLTransport` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Exact strategy transport between the Pauli game and its binary CL form. Question content has a canonical ambient encoding, with unused registers set to zero. This encoding inverts the decoder on every attained CL output. Consequently arbitrary strategies for the binary typed game pull back to the existing Pauli game with exactly the same state, dimensions, and value.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.QLD
--   open MIPRE.QLD.PauliCL
--   open Finset Classical
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
--   variable [Algebra (ZMod 2) F] [NeZero m] {t d : ℕ}
--
--   theorem MIPRE.QLD.PauliCL.pullbackStrategy_value (hm : m ∣ Fintype.card F)
--       (b : Module.Basis (Fin t) (ZMod 2) F)
--       (S : TensorProductStrategy (binaryGame (d := d) hm b)) :
--       (pullbackStrategy hm b S).value = S.value
--   ```
--
--   **Formalization Note** `MIPRE.QLD.PauliCL.pullbackStrategy_value` is declared in `MIPRE/Background/QLD/CLTransport.lean`, lines 129–149. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/CLTransport.lean#L129-L149; blueprint lem:intro-pauli-cl-content

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Definitions.Def_MIPRE_Background_QLD_CLTransport

open MIPRE
open MIPRE.QLD
open MIPRE.QLD.PauliCL
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [Algebra (ZMod 2) F] [NeZero m] {t d : ℕ}

theorem MIPRE.QLD.PauliCL.pullbackStrategy_value (hm : m ∣ Fintype.card F)
    (b : Module.Basis (Fin t) (ZMod 2) F)
    (S : TensorProductStrategy (binaryGame (d := d) hm b)) :
    (pullbackStrategy hm b S).value = S.value := by sorry
