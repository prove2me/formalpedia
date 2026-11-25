-- Prove2me | Theorems.Thm_GlobalTheory_Nef_PathJet_deriv_comp_m
-- name    : GlobalTheory.Nef.PathJet.deriv_comp_m
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:00:45.14057+00:00
-- url     : https://prove2.me/theorems/08b2e515-31da-4fff-b314-f6b84f8de068
-- title:
--   Path Jet: deriv comp m
-- statement:
--   The Path Jet construction uses the deriv comp m property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivCompM.lean#L26-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivCompM.lean#L26-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivCompM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.PathJet
open PowerSeries
variable {A B R : Type} [CommRing A] [CommRing B] [CommRing R]

theorem GlobalTheory.Nef.PathJet.deriv_comp_m (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (E : A →+ R)
    (hεπ : ε.comp π = RingHom.id B) (hmπ : m.comp π = π)
    (hm2 : ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2)
    (hE : ∀ f g, E (f * g) = β (ε f) * E g + β (ε g) * E f) (hEπ : ∀ a, E (π a) = 0) (f : A) :
    E (m f) = 2 * E f := by sorry
