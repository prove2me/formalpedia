-- Prove2me | Theorems.Thm_GlobalTheory_ZM_DwModel_isGaloisCover_field
-- name    : GlobalTheory.ZM.DwModel.isGaloisCover_field
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:01.77767+00:00
-- url     : https://prove2.me/theorems/89da769f-1d00-4c74-b018-c2286b41e143
-- title:
--   Dw Model: is Galois Cover field
-- statement:
--   The Dw Model construction uses the is Galois Cover field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/NotIsGaloisCoverTrivial.lean#L24-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/NotIsGaloisCoverTrivial.lean#L24-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_NotIsGaloisCoverTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.DwModel

theorem GlobalTheory.ZM.DwModel.isGaloisCover_field (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    IsGaloisCover (L ≃ₐ[K] L) (fun σ => spMap (σ : L →+* L)) (spMap (algebraMap K L)) := by sorry
