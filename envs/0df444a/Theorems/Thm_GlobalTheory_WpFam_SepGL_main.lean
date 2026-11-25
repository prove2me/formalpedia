-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_SepGL_main
-- name    : GlobalTheory.WpFam.SepGL.main
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:11.89442+00:00
-- url     : https://prove2.me/theorems/f0fcff6d-3d96-4d7f-9008-0f415fc8f486
-- title:
--   Sep GL: main
-- statement:
--   The Sep GL construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VmulNeZero.lean#L20-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VmulNeZero.lean#L20-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfWeierstrassPDerivWeierstrassPTorsionEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VmulNeZero
import Theorems.Thm_GlobalTheory_WpFam_TorsMem_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.SepGL

theorem GlobalTheory.WpFam.SepGL.main : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (α β : GL (Fin 2) (ZMod N)), (∀ i : Fin 2, wp N (vmul (Pi.single i 1) α) τ = wp N (vmul (Pi.single i 1) β) τ ∧ wpd N (vmul (Pi.single i 1) α) τ = wpd N (vmul (Pi.single i 1) β) τ) → α = β := by sorry
