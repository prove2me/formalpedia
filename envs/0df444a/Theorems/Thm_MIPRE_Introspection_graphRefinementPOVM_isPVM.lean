-- Prove2me | Theorems.Thm_MIPRE_Introspection_graphRefinementPOVM_isPVM
-- name    : MIPRE.Introspection.graphRefinementPOVM_isPVM
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:04:16.422589+00:00
-- url     : https://prove2.me/theorems/7e5a2abe-c413-4ba1-8d72-73b084dd8943
-- title:
--   Lemma graphRefinementPOVM_isPVM of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.AnswerRefinement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Deterministic graph refinement of measurement answers. The old answer is retained verbatim while its deterministic coordinate is recorded in a first component. Thus every old operator occurs exactly once; the construction preserves projectivity and all commutator sums exactly.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix Classical
--   variable {A C D K B : Type*} [Fintype A] [DecidableEq A]
--
--   theorem MIPRE.Introspection.graphRefinementPOVM_isPVM (M : POVM A D) (c : A → C)
--       (hM : IsPVM (fun a => (M.mats a).val)) :
--       IsPVM (fun p => ((graphRefinementPOVM M c).mats p).val)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.graphRefinementPOVM_isPVM` is declared in `MIPRE/Foundations/Introspection/AnswerRefinement.lean`, lines 95–98. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AnswerRefinement.lean#L95-L98; blueprint lem:intro-answer-refinement

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
import Definitions.Def_MIPRE_Foundations_Introspection_AnswerRefinement

open MIPRE
open MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {A C D K B : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

theorem MIPRE.Introspection.graphRefinementPOVM_isPVM (M : POVM A D) (c : A → C)
    (hM : IsPVM (fun a => (M.mats a).val)) :
    IsPVM (fun p => ((graphRefinementPOVM M c).mats p).val) := by sorry
