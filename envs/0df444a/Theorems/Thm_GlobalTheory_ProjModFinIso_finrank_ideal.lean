-- Prove2me | Theorems.Thm_GlobalTheory_ProjModFinIso_finrank_ideal
-- name    : GlobalTheory.ProjModFinIso.finrank_ideal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:54:56.342951+00:00
-- url     : https://prove2.me/theorems/1ae12f53-d84d-4bb8-97a2-dc9ad503fffb
-- title:
--   Proj Mod Fin Iso: finrank ideal
-- statement:
--   The Proj Mod Fin Iso construction uses the finrank ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FinitelyManyIsoClassesProjectiveNumberField.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FinitelyManyIsoClassesProjectiveNumberField.lean#L23-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.ProjModFinIso
variable {R : Type} [CommRing R] [IsDedekindDomain R]

theorem GlobalTheory.ProjModFinIso.finrank_ideal (I : Ideal R) (h : I ≠ ⊥) : Module.finrank R I = 1 := by sorry
