-- Prove2me | Theorems.Thm_GlobalTheory_CotUniv_smul_sqKer
-- name    : GlobalTheory.CotUniv.smul_sqKer
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:26:57.2584+00:00
-- url     : https://prove2.me/theorems/0ef3bd86-dd67-46ba-9050-5f91a25c41c0
-- title:
--   Cot Univ: smul sq Ker
-- statement:
--   The Cot Univ construction uses the smul sq Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L138-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/UniversalDerivation.lean#L138-L145

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

theorem GlobalTheory.CotUniv.smul_sqKer (r : R₀) (m : M) :
    r • (sqKer m : (sqProj O M).ker) = sqKer (algebraMap R₀ (O : Type) r • m) := by sorry
