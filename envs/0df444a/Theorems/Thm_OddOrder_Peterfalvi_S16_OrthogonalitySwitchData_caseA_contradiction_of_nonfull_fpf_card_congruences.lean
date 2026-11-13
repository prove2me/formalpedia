-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_caseA_contradiction_of_nonfull_fpf_card_congruences
-- name    : OddOrder.Peterfalvi.S16.OrthogonalitySwitchData.caseA_contradiction_of_nonfull_fpf_card_congruences
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:35:43.296212+00:00
-- url     : https://prove2.me/theorems/0b96e786-f4ca-469f-8fc4-886e954bb6b9
-- title:
--   Peterfalvi (14.15): the non-full case-(a) branch is contradictory under the fixed-point-free congruences
-- statement:
--   Throughout, `hyp.base` is the underlying `OddOrder.Peterfalvi.S15.Hypothesis`, and $p,q,u,v,h$ denote its parameters `hyp.base.p`, `hyp.base.q`, `hyp.base.u`, `hyp.base.v` (resp. `nc.h` for the `NonConjugateHypothesis`).
--
--   Let $G$ be a finite group which is minimal simple odd-order, `hyp` a Peterfalvi §14 configuration, `nc : NonConjugateHypothesis hyp`, `data : OrthogonalitySwitchData nc`, and `Sdata : CaseBForSData hyp`. Assume case (a) of the orthogonality switch (`data.caseA`) and
--
--   - $u \neq (p^q-1)/(p-1)$ (natural-number division);
--   - $u \mid h$;
--   - $h \equiv 1 \pmod p$ and $h\equiv 1\pmod q$;
--   - $u \equiv 1 \pmod q$.
--
--   Then we obtain a contradiction:
--   $$\text{False}.$$
--
--   This is the fixed-point-free cardinal-congruence form of the non-full case-(a) branch: for any quotient decomposition $h = ux$ the congruences give $x \equiv 1 \pmod q$, which leads to the displayed $x = q + np$ computation in (14.15).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/BetaVanishing.lean#L885-L909

import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupM
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentEtaOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_BetaVanishing

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace OrthogonalitySwitchData

theorem caseA_contradiction_of_nonfull_fpf_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_not_full :
      hyp.base.u ≠ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q]) :
    False := by sorry

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16
