-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_cyclotomic_ratio_gt_of_q_lt_p
-- name    : OddOrder.Peterfalvi.S16.cyclotomic_ratio_gt_of_q_lt_p
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:27:17.923989+00:00
-- url     : https://prove2.me/theorems/aa011084-9a48-4a6d-a37e-03089bdb65d5
-- title:
--   Peterfalvi (14.8): $\frac{(q^p-1)/(q-1)-1}{p}>\frac{(p^q-1)/(p-1)-1}{q}$ for odd primes $q<p$
-- statement:
--   Let $p, q$ be odd primes with $q<p$. Then, in $\mathbb{Q}$,
--   $$\frac{\dfrac{q^p-1}{q-1}-1}{p} \;>\; \frac{\dfrac{p^q-1}{p-1}-1}{q},$$
--   where the two quotients $(q^p-1)/(q-1)$ and $(p^q-1)/(p-1)$ are natural-number divisions, then $1$ is subtracted in $\mathbb{N}$ and the result cast to $\mathbb{Q}$.
--
--   This is the arithmetic bridge for Peterfalvi (14.8) under $q<p$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequalityArithmetic.lean#L244-L294

import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone
import Definitions.Def_OddOrder_Peterfalvi_S16_CoreLemmas

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

theorem cyclotomic_ratio_gt_of_q_lt_p {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q) (hqp : q < p) :
    (((q ^ p - 1) / (q - 1) - 1 : ℕ) : ℚ) / (p : ℚ) >
      (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) / (q : ℚ) := by sorry

end OddOrder.Peterfalvi.S16
