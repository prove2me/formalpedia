-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_PolyFn_algProd
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.PolyFn.algProd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:18:16.667503+00:00
-- url     : https://prove2.me/theorems/68e95ca1-f7cc-46be-a81b-5af99ae8a8f0
-- title:
--   Poly Fn: alg Prod
-- statement:
--   The Poly Fn construction uses the alg Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InfinitesimalCharacterStatement.lean#L68-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InfinitesimalCharacterStatement.lean#L68-L76

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatementStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
open _root_.CompanionTheory.RgExh _root_.CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet qminor Tm)
variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.PolyFn.algProd {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ}
    (h : ∀ i, PolyFn (fun u => algebraMap ℂ A (f i u))) :
    PolyFn (fun u => algebraMap ℂ A (∏ i ∈ s, f i u)) := by sorry
