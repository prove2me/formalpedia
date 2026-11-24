-- Prove2me | Theorems.Thm_GlobalTheory_ringHom_formallyEtale_respectsIso
-- name    : GlobalTheory.ringHom_formallyEtale_respectsIso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:06.302066+00:00
-- url     : https://prove2.me/theorems/4f27ed16-1941-4fca-859b-a9fc13c93f58
-- title:
--   Global Theory: ring Hom formally Etale respects Iso
-- statement:
--   The Global Theory construction uses the ring Hom formally Etale respects Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes.lean#L14-L20

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

theorem GlobalTheory.ringHom_formallyEtale_respectsIso : RingHom.RespectsIso.{u} @RingHom.FormallyEtale := by sorry
