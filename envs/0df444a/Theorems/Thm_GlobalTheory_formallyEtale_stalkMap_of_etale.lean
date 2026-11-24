-- Prove2me | Theorems.Thm_GlobalTheory_formallyEtale_stalkMap_of_etale
-- name    : GlobalTheory.formallyEtale_stalkMap_of_etale
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:53:17.401868+00:00
-- url     : https://prove2.me/theorems/7fecfdc7-63c3-4332-8689-bdb699650cbf
-- title:
--   Global Theory: formally Etale stalk Map of etale
-- statement:
--   The Global Theory construction uses the formally Etale stalk Map of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes.lean#L36-L40

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

theorem GlobalTheory.formallyEtale_stalkMap_of_etale {X Y : Scheme.{0}} (g : X ⟶ Y) [Etale g] (x : X) :
    (g.stalkMap x).hom.FormallyEtale := by sorry
