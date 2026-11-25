-- Prove2me | Theorems.Thm_GlobalTheory_CechMixed_exists_split
-- name    : GlobalTheory.CechMixed.exists_split
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:18:46.614239+00:00
-- url     : https://prove2.me/theorems/97b54399-688a-5588-a50f-f14102137daa
-- title:
--   Cech Mixed: exists split
-- statement:
--   The Cech Mixed construction uses the exists split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCechOneCocycleOnAffineCoverMixed.lean#L25-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCechOneCocycleOnAffineCoverMixed.lean#L25-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCechOneCocycleOnAffineCoverMixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
open GlobalTheory GlobalTheory.CechMixed
open GlobalTheory.KS

theorem GlobalTheory.CechMixed.exists_split {X : Scheme.{0}} {J : Type} {V : J → X.Opens} (hV : ⨆ i, V i = ⊤) {O : X.Opens}
    (hO : IsAffineOpen O) {z : C1 V} (hz : IsCoc V z) :
    ∃ b : ∀ i, Γ(X, V i ⊓ O), ∀ i i' (W : X.Opens), W ≤ V i → W ≤ V i' → W ≤ O →
      rsT (z i i') W = rsT (b i) W - rsT (b i') W := by sorry
