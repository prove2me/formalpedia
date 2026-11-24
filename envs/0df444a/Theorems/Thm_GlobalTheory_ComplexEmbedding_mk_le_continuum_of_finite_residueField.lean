-- Prove2me | Theorems.Thm_GlobalTheory_ComplexEmbedding_mk_le_continuum_of_finite_residueField
-- name    : GlobalTheory.ComplexEmbedding.mk_le_continuum_of_finite_residueField
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:25:32.032172+00:00
-- url     : https://prove2.me/theorems/cb0c8d8a-ac0f-49be-a0bb-6febb4aa1469
-- title:
--   Complex Embedding: mk le continuum of finite residue Field
-- statement:
--   The Complex Embedding construction uses the mk le continuum of finite residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComplexEmbeddingFractionFieldCdvr.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsComplexEmbeddingFractionFieldCdvr.lean#L9-L24

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComplexEmbeddingFractionFieldCdvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj
open GlobalTheory GlobalTheory.ComplexEmbedding
open Cardinal IsLocalRing

theorem GlobalTheory.ComplexEmbedding.mk_le_continuum_of_finite_residueField (V : Type) [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] [Finite (ResidueField V)] : #V ≤ 𝔠 := by sorry
