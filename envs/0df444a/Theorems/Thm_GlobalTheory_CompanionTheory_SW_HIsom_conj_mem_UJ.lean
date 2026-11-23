-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HIsom_conj_mem_UJ
-- name    : GlobalTheory.CompanionTheory.SW.HIsom.conj_mem_UJ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:36.891269+00:00
-- url     : https://prove2.me/theorems/0021ff7a-b1e8-4980-973b-0a7b25d92b88
-- title:
--   HIsom: conj mem UJ
-- statement:
--   The HIsom construction uses the conj mem UJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryIsomOfIsometry.lean#L15-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryIsomOfIsometry.lean#L15-L33

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryIsomOfIsometry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HIsom
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.CompanionTheory.SW.HIsom.conj_mem_UJ (s : A →+* A) (J : Matrix n n A) (G u : GL n A)
    (hu : u ∈ UJ s (cT s (G : Matrix n n A) * J * (G : Matrix n n A))) :
    G * u * G⁻¹ ∈ UJ s J := by sorry
