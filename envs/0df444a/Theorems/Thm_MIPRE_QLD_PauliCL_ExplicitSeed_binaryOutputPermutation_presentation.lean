-- Prove2me | Theorems.Thm_MIPRE_QLD_PauliCL_ExplicitSeed_binaryOutputPermutation_presentation
-- name    : MIPRE.QLD.PauliCL.ExplicitSeed.binaryOutputPermutation_presentation
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:06:45.436447+00:00
-- url     : https://prove2.me/theorems/310d4b95-3d1c-4d47-a8fc-1f9f2f7ce7dc
-- title:
--   Lemma binaryOutputPermutation_presentation of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Background.QLD.CLExplicitTransport` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Equivalences between explicit and legacy Pauli question contents. Only line questions carry the seed. Permuting that coordinate on their raw contents gives a genuine equivalence, including contents outside the support of the sampler. The same permutation of the shared random seed intertwines all twenty-six sampled question maps simultaneously.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.QLD
--   open MIPRE.QLD.PauliCL
--   open MIPRE.QLD.PauliCL.ExplicitSeed
--   open Finset Classical
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
--   variable [NeZero m]
--   variable [Algebra (ZMod 2) F] {t : ℕ}
--
--   theorem MIPRE.QLD.PauliCL.ExplicitSeed.binaryOutputPermutation_presentation (hm : m ∣ Fintype.card F)
--       (χ : F → Fin m) (π : F ≃ F) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
--       (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty)
--       (x : Fin ((3*m+3)*t) → ZMod 2) :
--       binaryOutputPermutation π b T ((binaryPresentation χ b T).eval x) =
--         (PauliCL.binaryPresentation hm b T).eval (binarySeedPermutation π b x)
--   ```
--
--   **Formalization Note** `MIPRE.QLD.PauliCL.ExplicitSeed.binaryOutputPermutation_presentation` is declared in `MIPRE/Background/QLD/CLExplicitTransport.lean`, lines 87–104. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/CLExplicitTransport.lean#L87-L104; blueprint lem:intro-explicit-selector-questions

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
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
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
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
import Definitions.Def_MIPRE_Background_QLD_CLExplicitSeed
import Definitions.Def_MIPRE_Background_QLD_CLExplicitTransport

open MIPRE
open MIPRE.QLD
open MIPRE.QLD.PauliCL
open MIPRE.QLD.PauliCL.ExplicitSeed
open Finset Classical
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}
variable [NeZero m]
variable [Algebra (ZMod 2) F] {t : ℕ}

theorem MIPRE.QLD.PauliCL.ExplicitSeed.binaryOutputPermutation_presentation (hm : m ∣ Fintype.card F)
    (χ : F → Fin m) (π : F ≃ F) (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
    (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty)
    (x : Fin ((3*m+3)*t) → ZMod 2) :
    binaryOutputPermutation π b T ((binaryPresentation χ b T).eval x) =
      (PauliCL.binaryPresentation hm b T).eval (binarySeedPermutation π b x) := by sorry
