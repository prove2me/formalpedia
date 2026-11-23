-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryStd_basis_apply
-- name    : GlobalTheory.UnitaryStd.basis_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:20.714794+00:00
-- url     : https://prove2.me/theorems/13d4437c-70f1-46bc-b686-34e3e58ea5fb
-- title:
--   Unitary Std: basis apply
-- statement:
--   The Unitary Std construction uses the basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisApply.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisApply.lean#L108-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open GlobalTheory GlobalTheory.UnitaryStd
variable {r g : ℕ}
variable {E : Type} [Field E] [NumberField E] (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ)
variable {ρ g}
variable (ρ g)

theorem GlobalTheory.UnitaryStd.basis_apply (p : Fin r × (Fin g ⊕ Fin g)) (i : Fin r) :
    basis ρ g p i = (fun k => Pi.single (M := fun _ => ℤ) p 1 (i, Sum.inl k),
      fun k => Pi.single (M := fun _ => ℤ) p 1 (i, Sum.inr k)) := by sorry
