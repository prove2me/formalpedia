-- Prove2me | Theorems.Thm_GroundTheory_Global_cycHerbrand_eq_of_surjective_of_finite_ker
-- name    : GroundTheory.Global.cycHerbrand_eq_of_surjective_of_finite_ker
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:01.005706+00:00
-- url     : https://prove2.me/theorems/007ddc77-e53e-4955-af63-6f7935998a1b
-- title:
--   Global: cyc Herbrand eq of surjective of finite ker
-- statement:
--   The Global construction uses the cyc Herbrand eq of surjective of finite ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsExact.lean#L51-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/SUnitsExact.lean#L51-L82

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {G A B C : Type*} [Group G] [Fintype G] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C]

theorem GroundTheory.Global.cycHerbrand_eq_of_surjective_of_finite_ker (ρB : Representation ℤ G B)
    (ρC : Representation ℤ G C) (σ : G) {p : B →+ C} (hp : Function.Surjective p)
    [Finite p.ker] (hpG : ∀ g b, p (ρB g b) = ρC g (p b))
    (hC : HasHerbrandQuotient (cycSubOne ρC σ) (cycNorm ρC)) :
    cycHerbrand ρB σ = cycHerbrand ρC σ := by sorry
