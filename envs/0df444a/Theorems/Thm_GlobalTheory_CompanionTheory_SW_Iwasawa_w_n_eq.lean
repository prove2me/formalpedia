-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Iwasawa_w_n_eq
-- name    : GlobalTheory.CompanionTheory.SW.Iwasawa.w_n_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:25.959937+00:00
-- url     : https://prove2.me/theorems/ce8e4c00-7c91-45f3-b22c-c960af59550f
-- title:
--   Iwasawa: w n eq
-- statement:
--   The Iwasawa construction uses the w n eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IwasawaDecompositionAdelicSL2.lean#L134-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IwasawaDecompositionAdelicSL2.lean#L134-L155

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IwasawaDecompositionAdelicSL2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Iwasawa
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.Iwasawa.w_n_eq {R : Type} [CommRing R] (β e : R) (u : Rˣ) (k : SL(2, R))
    (h00 : k 0 0 = e - 1) (h01 : k 0 1 = e) (h10 : k 1 0 = -(u : R))
    (h11 : k 1 1 = -((u : R) * β)) (h : (u : R) * e + (1 - e) * ((u : R) * β) = 1) :
    wMat * nMat β = nMat ((e - 1) * (u : R)) * mMat u * k := by sorry
