-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_CaseBForSData_two_q_lt_u
-- name    : OddOrder.Peterfalvi.S16.CaseBForSData.two_q_lt_u
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:19:23.42441+00:00
-- url     : https://prove2.me/theorems/e07e9352-4f43-4f90-a040-628a79eedba7
-- title:
--   Peterfalvi (14.6): in the $S$-side case (9.7.b), $u>2q$
-- statement:
--   Let `hyp` be a Peterfalvi §14 configuration with $q=$ `hyp.base.q` and $u=$ `hyp.base.u`, and let `data : CaseBForSData hyp` be the $S$-side case-(9.7.b) data. Then
--   $$2q < u .$$
--
--   This is the size input from the $S$-side cyclotomic value consumed by the norm-cascade contradiction in (14.11.4).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequality.lean#L212-L260

import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace CaseBForSData

theorem two_q_lt_u {hyp : Hypothesis (G := G)} (data : CaseBForSData hyp) :
    2 * hyp.base.q < hyp.base.u := by sorry

end CaseBForSData

end OddOrder.Peterfalvi.S16
