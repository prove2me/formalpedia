-- Prove2me | Theorems.Thm_GlobalTheory_ringHom_formallyEtale_of_ringEquiv
-- name    : GlobalTheory.ringHom_formallyEtale_of_ringEquiv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:18:38.588551+00:00
-- url     : https://prove2.me/theorems/3203d113-322d-472a-81a8-2a024df218a6
-- title:
--   Global Theory: ring Hom formally Etale of ring Equiv
-- statement:
--   The Global Theory construction uses the ring Hom formally Etale of ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes.lean#L8-L12

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

theorem GlobalTheory.ringHom_formallyEtale_of_ringEquiv {S T : Type u} [CommRing S] [CommRing T]
    (e : S ≃+* T) : (e : S →+* T).FormallyEtale := by sorry
