-- Prove2me | Theorems.Thm_GlobalTheory_preirreducibleSpace_tensor_congr_fibreChart
-- name    : GlobalTheory.preirreducibleSpace_tensor_congr_fibreChart
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:26.656676+00:00
-- url     : https://prove2.me/theorems/95880b98-2c00-4d5f-b69c-e72c7941879b
-- title:
--   Global Theory: preirreducible Space tensor congr fibre Chart
-- statement:
--   The Global Theory construction uses the preirreducible Space tensor congr fibre Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleFibreStandardEtaleSpreads.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleFibreStandardEtaleSpreads.lean#L16-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HypersurfacePartGeometricIrreducibleSpreadsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StandardEtaleMvPolynomialHypersurfaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceFibreHypersurfaceSpectrumIffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleFibreStandardEtaleSpreads
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory

theorem GlobalTheory.preirreducibleSpace_tensor_congr_fibreChart (A B C k : Type) [CommRing A] [CommRing B]
    [CommRing C] [CommRing k] [Algebra A B] [Algebra A C] [Algebra A k] (e : B ≃ₐ[A] C) :
    PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) ↔ PreirreducibleSpace (PrimeSpectrum (k ⊗[A] C)) := by sorry
