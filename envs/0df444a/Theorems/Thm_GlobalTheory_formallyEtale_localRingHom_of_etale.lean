-- Prove2me | Theorems.Thm_GlobalTheory_formallyEtale_localRingHom_of_etale
-- name    : GlobalTheory.formallyEtale_localRingHom_of_etale
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:53:11.170069+00:00
-- url     : https://prove2.me/theorems/d6edccd1-5cb1-4c33-9452-a5c9416b3d41
-- title:
--   Global Theory: formally Etale local Ring Hom of etale
-- statement:
--   The Global Theory construction uses the formally Etale local Ring Hom of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes.lean#L22-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes.lean#L22-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory
universe u

theorem GlobalTheory.formallyEtale_localRingHom_of_etale {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Etale) (J : Ideal S) [J.IsPrime] :
    (Localization.localRingHom (J.comap f) J f rfl).FormallyEtale := by sorry
