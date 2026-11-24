-- Prove2me | Theorems.Thm_GlobalTheory_CotUniv_map_sqMap_tg
-- name    : GlobalTheory.CotUniv.map_sqMap_tg
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:27:21.21522+00:00
-- url     : https://prove2.me/theorems/018da31a-b198-4947-b63e-c758dfe19215
-- title:
--   Cot Univ: map sq Map tg
-- statement:
--   The Cot Univ construction uses the map sq Map tg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L156-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L156-L162

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_UniversalDerivation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory GlobalTheory.CotUniv
variable {R₀ : Type} [CommRing R₀] (O : LAlg R₀)
  (M : Type) [AddCommGroup M] [Module (O : Type) M]
variable {O M}
variable (O M)
variable {O M}
variable {M' : Type} [AddCommGroup M'] [Module (O : Type) M']

theorem GlobalTheory.CotUniv.map_sqMap_tg (B : BX R₀) {ι : Type} [Fintype ι] (w : ι → B.gg) (m : ι → M)
    (u : M →ₗ[(O : Type)] M') :
    B.map (sqMap u) (B.tg (sqProj O M) (sqProj_sqZero O M) (∑ k, w k ⊗ₜ[R₀] sqKer (m k))) =
      B.tg (sqProj O M') (sqProj_sqZero O M') (∑ k, w k ⊗ₜ[R₀] sqKer (u (m k))) := by sorry
