-- Prove2me | Theorems.Thm_GlobalTheory_MuTowerInj_iota_mul
-- name    : GlobalTheory.MuTowerInj.iota_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:28:15.748864+00:00
-- url     : https://prove2.me/theorems/18c7f231-4478-4e6c-8a45-998efe6911a3
-- title:
--   Mu Tower Inj: iota mul
-- statement:
--   The Mu Tower Inj construction uses the iota mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MuCocycleCoboundaryLift.lean#L155-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MuCocycleCoboundaryLift.lean#L155-L167

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MuCocycleCoboundaryLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory GlobalTheory.MuTowerInj
variable (l : ℕ) [Fact l.Prime] (n : ℕ)

theorem GlobalTheory.MuTowerInj.iota_mul (u : ℤ_[l]) (b : ZMod (l ^ 1)) :
    iota l n (PadicInt.toZModPow 1 u * b) = PadicInt.toZModPow (n + 1) u * iota l n b := by sorry
