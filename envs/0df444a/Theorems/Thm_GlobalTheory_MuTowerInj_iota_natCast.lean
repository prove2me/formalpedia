-- Prove2me | Theorems.Thm_GlobalTheory_MuTowerInj_iota_natCast
-- name    : GlobalTheory.MuTowerInj.iota_natCast
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:32.346555+00:00
-- url     : https://prove2.me/theorems/7d82c68c-531e-40b7-b7ab-5b2772fb4544
-- title:
--   Mu Tower Inj: iota nat Cast
-- statement:
--   The Mu Tower Inj construction uses the iota nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MuCocycleCoboundaryLift.lean#L143-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MuCocycleCoboundaryLift.lean#L143-L144

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

theorem GlobalTheory.MuTowerInj.iota_natCast (x : ℕ) : iota l n x = ((l ^ n * x : ℕ) : ZMod (l ^ (n + 1))) := by sorry
