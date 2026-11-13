-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_TypeIOverNormalizerData_prime_dvd_sq_sub_one_of_omega1Center
-- name    : OddOrder.Peterfalvi.S15.TypeIOverNormalizerData.prime_dvd_sq_sub_one_of_omega1Center
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:10:32.174585+00:00
-- url     : https://prove2.me/theorems/7193d677-35db-4d6d-b125-a502ef433d34
-- title:
--   Peterfalvi (14.6): $p\mid r^2-1$ when $|\Omega_1(Z(R))|\in\{r,r^2\}$
-- statement:
--   Let $G$ be a finite group and `hyp : Hypothesis (G := G)` the Peterfalvi Section 13 hypothesis package with parameter $p=$ `hyp.p`, and let `data : TypeIOverNormalizerData hyp` be the type-I maximal-subgroup data over $N_G(U)$ from (13.17)/(14.5), with Fitting kernel $H=$ `data.H`. Let $r$ be a prime and $R$ a Sylow $r$-subgroup of $H$. If $|\Omega_1(Z(R))|=r$ or $|\Omega_1(Z(R))|=r^2$, then
--   $$p\ \mid\ r^2-1 .$$
--
--   Here $\Omega_1(Z(R))$ is formed in $G$ (`omega1CenterInG` of the image of $R$). The conjugate $W_2^y$ of order $p$ acts fixed-point-freely on $\Omega_1(Z(R))$, giving this divisibility in Peterfalvi (14.6).
--
--   **Formalization Note.** $r^2-1$ is a natural-number subtraction.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CaseAOmegaFixedPointFree.lean#L82-L151

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

theorem TypeIOverNormalizerData.prime_dvd_sq_sub_one_of_omega1Center [Finite G]
    {hyp : Hypothesis (G := G)} (data : TypeIOverNormalizerData hyp)
    {r : ℕ} (hr : r.Prime) (R : Sylow r ↥data.H)
    (hcard :
      Nat.card ↥(OddOrder.BG.Ch3.S10.omega1CenterInG
        ((R : Subgroup ↥data.H).map data.H.subtype) r) = r ∨
      Nat.card ↥(OddOrder.BG.Ch3.S10.omega1CenterInG
        ((R : Subgroup ↥data.H).map data.H.subtype) r) = r ^ 2) :
    hyp.p ∣ r ^ 2 - 1 := by sorry

end OddOrder.Peterfalvi.S15
