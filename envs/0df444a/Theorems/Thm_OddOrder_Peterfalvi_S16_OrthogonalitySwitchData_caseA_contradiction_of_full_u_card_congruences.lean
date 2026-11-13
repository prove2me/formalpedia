-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_caseA_contradiction_of_full_u_card_congruences
-- name    : OddOrder.Peterfalvi.S16.OrthogonalitySwitchData.caseA_contradiction_of_full_u_card_congruences
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:36:41.409207+00:00
-- url     : https://prove2.me/theorems/5ed07739-5a8f-4e4a-b66d-14bf065abfd2
-- title:
--   Peterfalvi (14.16): case (a) is contradictory when $H > U$ and $u$ takes its full cyclotomic value
-- statement:
--   Throughout, `hyp.base` is the underlying `OddOrder.Peterfalvi.S15.Hypothesis`, and $p,q,u,v,h$ denote its parameters `hyp.base.p`, `hyp.base.q`, `hyp.base.u`, `hyp.base.v` (resp. `nc.h` for the `NonConjugateHypothesis`).
--
--   Let $G$ be a finite minimal simple odd-order group, `hyp` a Peterfalvi §14 configuration, `nc : NonConjugateHypothesis hyp`, `data : OrthogonalitySwitchData nc`, `Sdata : CaseBForSData hyp`. Assume case (a) (`data.caseA`) and
--
--   - $u = (p^q-1)/(p-1)$ (natural-number division);
--   - $u \mid h$;
--   - $h\equiv 1\pmod p$, $h\equiv1\pmod q$, and $u\equiv 1\pmod q$;
--   - for every natural number $x$ with $h = u x$ one has $x\ne 1$.
--
--   Then
--   $$\text{False}.$$
--
--   Informally: $x\equiv 1 \pmod{pq}$ and $x$ odd with $x\neq 1$ give $x>2pq$; the case-(a) bound then forces $2u<pq$, contradicting $u\equiv 1\pmod {pq}$ and $u>2q$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/BetaVanishing.lean#L911-L1023

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

theorem caseA_contradiction_of_full_u_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (data : OrthogonalitySwitchData nc) (Sdata : CaseBForSData hyp)
    (hcaseA : data.caseA)
    (hu_full : hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q])
    (hx_ne_one_of_quotient : ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1) :
    False := by sorry

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16
