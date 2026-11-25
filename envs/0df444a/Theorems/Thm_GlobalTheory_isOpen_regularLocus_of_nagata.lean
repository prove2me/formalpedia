-- Prove2me | Theorems.Thm_GlobalTheory_isOpen_regularLocus_of_nagata
-- name    : GlobalTheory.isOpen_regularLocus_of_nagata
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:25.605598+00:00
-- url     : https://prove2.me/theorems/dee8e567-b968-4920-8c1e-cd6eda85b5ea
-- title:
--   Global Theory: is Open regular Locus of nagata
-- statement:
--   The Global Theory construction uses the is Open regular Locus of nagata property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenRegularLocusOfNagata.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenRegularLocusOfNagata.lean#L33-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyOpenStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularNearOfRegularQuotientPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenRegularLocusOfNagata
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.isOpen_regularLocus_of_nagata : ∀ (B : Type) [CommRing B] [IsNoetherianRing B], (∀ (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q)))) → IsOpen {Q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime Q.asIdeal)} := by sorry
