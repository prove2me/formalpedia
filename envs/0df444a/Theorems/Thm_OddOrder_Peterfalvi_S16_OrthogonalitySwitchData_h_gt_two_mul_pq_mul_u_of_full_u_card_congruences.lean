-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_OrthogonalitySwitchData_h_gt_two_mul_pq_mul_u_of_full_u_card_congruences
-- name    : OddOrder.Peterfalvi.S16.OrthogonalitySwitchData.h_gt_two_mul_pq_mul_u_of_full_u_card_congruences
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:35:45.23306+00:00
-- url     : https://prove2.me/theorems/fc8757df-1697-46e7-9857-05d08a55afbf
-- title:
--   Peterfalvi (14.16): $h > 2pq\,u$ when $u$ is the full cyclotomic value and $h\neq u$
-- statement:
--   Throughout, `hyp.base` is the underlying `OddOrder.Peterfalvi.S15.Hypothesis`, and $p,q,u,v,h$ denote its parameters `hyp.base.p`, `hyp.base.q`, `hyp.base.u`, `hyp.base.v` (resp. `nc.h` for the `NonConjugateHypothesis`).
--
--   Let `hyp` be a Peterfalvi §14 configuration, `nc : NonConjugateHypothesis hyp`, and assume
--
--   - $u = (p^q-1)/(p-1)$ (natural-number division);
--   - $u\mid h$;
--   - $h \equiv 1 \pmod p$, $h\equiv 1\pmod q$, $u\equiv 1\pmod q$;
--   - every natural number $x$ with $h = ux$ satisfies $x \ne 1$.
--
--   Then
--   $$2\,(p q)\,u \;<\; h .$$
--
--   Write $h = ux$. The congruences give $x\equiv 1 \pmod {pq}$; as $x \neq 1$ and $x$ is odd, $x > 2pq$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/BetaVanishing.lean#L1025-L1071

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

theorem h_gt_two_mul_pq_mul_u_of_full_u_card_congruences
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (hu_full : hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q])
    (hx_ne_one_of_quotient : ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1) :
    2 * (hyp.base.p * hyp.base.q) * hyp.base.u < nc.h := by sorry

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16
