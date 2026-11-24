-- Prove2me | Theorems.Thm_GlobalTheory_SW_ShortStep_map_proj
-- name    : GlobalTheory.SW.ShortStep.map_proj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:44:54.844172+00:00
-- url     : https://prove2.me/theorems/a4368960-bfb1-4298-98b0-ddac2bf6a216
-- title:
--   Short Step: map proj
-- statement:
--   The Short Step construction uses the map proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ShortIsotropicVectorsExistenceSuccOfVeryShortSte.lean#L347-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ShortIsotropicVectorsExistenceSuccOfVeryShortSte.lean#L347-L351

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ShortStep
open MinkowskiProductBounds
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}

theorem GlobalTheory.SW.ShortStep.map_proj {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (V w : Matrix (Fin 1) (Fin n) E) : (1 - G * wᴴ * V - G * Vᴴ * w).map τ =
      1 - G.map τ * (w.map τ)ᴴ * V.map τ - G.map τ * (V.map τ)ᴴ * w.map τ := by sorry
