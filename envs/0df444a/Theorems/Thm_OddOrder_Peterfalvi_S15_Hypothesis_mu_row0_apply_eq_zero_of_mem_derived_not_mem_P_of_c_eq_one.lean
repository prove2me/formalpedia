-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_mu_row0_apply_eq_zero_of_mem_derived_not_mem_P_of_c_eq_one
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.mu_row0_apply_eq_zero_of_mem_derived_not_mem_P_of_c_eq_one
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:57:31.722341+00:00
-- url     : https://prove2.me/theorems/92c45bf5-9efc-4241-a597-e25f5e54c73c
-- title:
--   Peterfalvi (13.18.a): $\mu_{0j}$ vanishes on $S'\setminus P$ when $c=1$
-- statement:
--   Let $G$ be a finite group which is a minimal simple odd-order group (`OddOrder.BG.IsMinimalSimpleOdd G`), and let `hyp` be a Peterfalvi §13 configuration for $G$ (`OddOrder.Peterfalvi.S15.Hypothesis`) with parameters $p, q$, subgroups $S, P, \dots$ and the class-function grid $\mu_{ij}$ on $S$. Assume the configuration's parameter $c$ equals $1$ (`hyp.c = 1`). Let $j \in \{0,\dots,p-1\}$ with $j \neq 0$, and let $z \in S$ with $z$ in the derived subgroup $S'$ of $S$ (taken inside $G$) but $z \notin P$. Then
--   $$\mu_{0j}(z) = 0 .$$
--
--   This is the vanishing of $\mu_{0j}$ on $S' - P$ used in the proof of Peterfalvi (13.18.a); it follows from the induction identity for the $\mu$-grid together with (13.3.a) and (13.12).
--
--   **Formalization Note.** Row and column indices are elements of `Fin hyp.q` and `Fin hyp.p`; "$0$" is `⟨0, _⟩`. The value is `hyp.mu 0 j z` where `z` has type `↥hyp.S`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean#L1314-L1410

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in

theorem Hypothesis.mu_row0_apply_eq_zero_of_mem_derived_not_mem_P_of_c_eq_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hc1 : hyp.c = 1)
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩)
    (z : ↥hyp.S) (hzD : (z : G) ∈ OddOrder.GroupTheory.derivedInG hyp.S)
    (hzP : (z : G) ∉ hyp.P) :
    hyp.mu ⟨0, hyp.q_prime.pos⟩ j z = 0 := by sorry

end OddOrder.Peterfalvi.S15
