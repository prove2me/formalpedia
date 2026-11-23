-- Prove2me | Theorems.Thm_GlobalTheory_surjective_of_fibre_rank
-- name    : GlobalTheory.surjective_of_fibre_rank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:56.008088+00:00
-- url     : https://prove2.me/theorems/1db44dc3-41a5-42f5-b2a8-13c59c5d3de8
-- title:
--   Global Theory: surjective of fibre rank
-- statement:
--   The Global Theory construction uses the surjective of fibre rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubsingletonOfResidueFieldFibres.lean#L21-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubsingletonOfResidueFieldFibres.lean#L21-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open TensorProduct
open TensorProduct
open TensorProduct

theorem GlobalTheory.surjective_of_fibre_rank (O M N : Type) [CommRing O] [AddCommGroup M]
    [Module O M] [AddCommGroup N] [Module O N] [Module.Finite O N] (f : M →ₗ[O] N)
    (h : ∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField
      (LinearMap.range (f.baseChange q.asIdeal.ResidueField)) =
      Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) :
    Function.Surjective f := by sorry
