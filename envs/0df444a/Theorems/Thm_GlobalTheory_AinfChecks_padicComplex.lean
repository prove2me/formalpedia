-- Prove2me | Theorems.Thm_GlobalTheory_AinfChecks_padicComplex
-- name    : GlobalTheory.AinfChecks.padicComplex
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:57:23.005207+00:00
-- url     : https://prove2.me/theorems/24490338-08f8-41e2-a3fe-1648d95c5108
-- title:
--   Ainf Checks: padic Complex
-- statement:
--   The Ainf Checks construction uses the padic Complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/NonemptyAlgebra.lean#L12-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/NonemptyAlgebra.lean#L12-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_NonemptyAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WittVector Ideal ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.AinfChecks
open WittVector Ideal

theorem GlobalTheory.AinfChecks.padicComplex (p : ℕ) [Fact p.Prime] :
    ∃ (_ : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p])) (_ : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]),
      (∃ pflat : PreTilt 𝓞_ℂ_[p] p, pflat.untilt = ((p : ℕ) : 𝓞_ℂ_[p])) ∧
      (∃ ε : PreTilt 𝓞_ℂ_[p] p,
        IsPrimitiveRoot (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε).untilt) p) ∧
      _root_.ReciprocityTheory.PGsh.KerThetaStatement p 𝓞_ℂ_[p] ∧ _root_.ReciprocityTheory.PGsh.XiNuStatement p ℂ_[p] Valued.v 𝓞_ℂ_[p] ∧
      _root_.ReciprocityTheory.PGsh.RegularStatement p 𝓞_ℂ_[p] ∧ _root_.ReciprocityTheory.PGsh.FlatW'Statement p 𝓞_ℂ_[p] := by sorry
