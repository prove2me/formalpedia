-- Prove2me | Theorems.Thm_GlobalTheory_CapelliCentral_prod_apply
-- name    : GlobalTheory.CapelliCentral.prod_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:11.827812+00:00
-- url     : https://prove2.me/theorems/1335b735-b2d0-4c2a-9c81-7eb78f902a31
-- title:
--   Capelli Central: prod apply
-- statement:
--   The Capelli Central construction uses the prod apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SmoothAddSmul.lean#L238-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SmoothAddSmul.lean#L238-L247

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SmoothAddSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CapelliCentral
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.CapelliCentral.prod_apply (l : List (ℂ × Fin n × Fin n)) (F : smoothSpace ε E)
    {f : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → F.1 g = f g) :
    ∀ g, inUJ ε g → ((l.map fun p => Tm (eabEnd ε E) p.1 p.2.1 p.2.2).prod F).1 g =
      (l.map fun p => Top (EabV ε) p.1 p.2.1 p.2.2).foldr (fun T h => T h) f g := by sorry
