-- Prove2me | Theorems.Thm_GlobalTheory_ClopenIdealSheaf_map_comap_eq
-- name    : GlobalTheory.ClopenIdealSheaf.map_comap_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:42:08.797318+00:00
-- url     : https://prove2.me/theorems/ac9e4926-d049-4090-850d-78626de3b971
-- title:
--   Clopen Ideal Sheaf: map comap eq
-- statement:
--   The Clopen Ideal Sheaf construction uses the map comap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealSheafDataOfIsClopenFamily.lean#L45-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealSheafDataOfIsClopenFamily.lean#L45-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSheafDataOfIsClopenFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.ClopenIdealSheaf

theorem GlobalTheory.ClopenIdealSheaf.map_comap_eq {Z : Scheme.{0}} (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U))
    {U V B : Z.affineOpens} (hVU : (V : Z.Opens) ≤ U) (f : Γ(Z, U))
    (hB : Z.affineBasicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f) = B)
    (hBD : (B : Z.Opens) ≤ Z.basicOpen f)
    (hI : (F V).map (Z.presheaf.map (homOfLE (Z.basicOpen_le
        ((Z.presheaf.map (homOfLE hVU).op).hom f))).op).hom =
      F (Z.affineBasicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f))) :
    ((F V).comap (Z.presheaf.map (homOfLE hVU).op).hom).map
        (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom =
      (F B).comap (Z.presheaf.map (homOfLE hBD).op).hom := by sorry
