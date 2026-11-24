-- Prove2me | Theorems.Thm_GlobalTheory_SignChar_ptMap_spec
-- name    : GlobalTheory.SignChar.ptMap_spec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:13:35.003805+00:00
-- url     : https://prove2.me/theorems/598f5da3-8002-4f24-8994-2e4be71ffd34
-- title:
--   Sign Char: pt Map spec
-- statement:
--   The Sign Char construction uses the pt Map spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PairingNsmulRight.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PairingNsmulRight.lean#L81-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvenTwoEvaluationSign
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PairingNsmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
noncomputable section
open GlobalTheory
open GlobalTheory.SignChar
variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

theorem GlobalTheory.SignChar.ptMap_spec (D : Dat p g B Tw Dt Oe σ cp) (t : Nb p g) :
    (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = LHom.id Tw.O ∧
      B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = ptOf B D.L.τ t := by sorry
