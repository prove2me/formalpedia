-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_Hypothesis_quotient_gt_two_mul_pq_of_modEq_one_mod_p_and_q
-- name    : OddOrder.Peterfalvi.S16.Hypothesis.quotient_gt_two_mul_pq_of_modEq_one_mod_p_and_q
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:27:16.336492+00:00
-- url     : https://prove2.me/theorems/9a860603-a987-4db7-9a35-aaa0f3b80b91
-- title:
--   Peterfalvi (14.16): an odd $x\neq1$ with $x\equiv1 \pmod p,\pmod q$ exceeds $2pq$
-- statement:
--   Let `hyp` be a Peterfalvi §14 configuration (`OddOrder.Peterfalvi.S16.Hypothesis`), with primes $p$ = `hyp.base.p` and $q$ = `hyp.base.q`. Let $x$ be a natural number with $x \equiv 1 \pmod p$, $x\equiv 1 \pmod q$, $x$ odd and $x\ne 1$. Then
--   $$2pq < x .$$
--
--   By the Chinese remainder theorem $x\equiv 1 \pmod{pq}$; since $x$ is odd and $x\ne1$ the smallest candidate is beyond $2pq$. This is the parity estimate for the quotient $x = h/u$ in (14.16).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_CoreLemmas.lean#L191-L233

import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Setup
import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacter
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S15_SSideGaloisFieldModel
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTGrid
import Definitions.Def_OddOrder_Peterfalvi_S16_CoreLemmas

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace Hypothesis

theorem quotient_gt_two_mul_pq_of_modEq_one_mod_p_and_q
    (hyp : Hypothesis (G := G)) {x : ℕ}
    (hx_mod_p : x ≡ 1 [MOD hyp.base.p])
    (hx_mod_q : x ≡ 1 [MOD hyp.base.q])
    (hx_odd : Odd x) (hx_ne_one : x ≠ 1) :
    2 * (hyp.base.p * hyp.base.q) < x := by sorry

end Hypothesis

end OddOrder.Peterfalvi.S16
