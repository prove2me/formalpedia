-- Prove2me | Theorems.Thm_GlobalTheory_GaugeDeriv_hPullW_toLeaf
-- name    : GlobalTheory.GaugeDeriv.hPullW_toLeaf
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:33:11.523798+00:00
-- url     : https://prove2.me/theorems/4da0c66c-7286-4146-a19c-156d234b7ecc
-- title:
--   Gauge Deriv: h Pull W to Leaf
-- statement:
--   The Gauge Deriv construction uses the h Pull W to Leaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PderivLeafGaugeEqPairingAddIntegral.lean#L81-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PderivLeafGaugeEqPairingAddIntegral.lean#L81-L109

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SubstEqOfCoeffEqOfKilled
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivLeafGaugeEqPairingAddIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
open GlobalTheory GlobalTheory.GaugeDeriv
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)]
variable {ι ι' : Type} [Fintype ι] [Fintype ι']
variable {V : VF C} {d : ℕ} {J : Fin 2 → Type} [∀ g, Fintype (J g)]

theorem GlobalTheory.GaugeDeriv.hPullW_toLeaf (G : ∀ g, Cart V d (I g) (J g)) (g : Fin 2) (a a' : ZMod d)
    (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (he : ∀ c x, (G g).ty (Sum.inl x) ≠ a → e c x = 0)
    (hv : ∀ b k, (G (1 - g)).ty (Sum.inl k) ≠ a' → v' b k = 0) (F : MvPowerSeries (WV I) C) :
    hPullW (toLeaf G g a a' F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) =
      hPullW F (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by sorry
