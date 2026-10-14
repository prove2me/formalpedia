-- Prove2me | Theorems.Thm_IntMul_HvdH_exactConv_eq
-- name    : IntMul.HvdH.exactConv_eq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T02:55:33.135458+00:00
-- url     : https://prove2.me/theorems/6622fc6f-c67a-477d-8587-636896f02094
-- title:
--   Exact integer convolution from approximate DFTs (Harvey–van der Hoeven §5.3)
-- statement:
--   Let $s_i<t_i$ be coprime for $i<d$ with $s_i\le\alpha^2(t_i-s_i)$, $\alpha\ge2$, and let $p$ satisfy the precision conditions of Theorem 4.1 (`thm_4_1_fp`). Let $F_t$ be any fixed-point oracle for the normalised DFT $\mathcal F_t$ on the box $\prod_i[0,t_i)$ (`dftBox`): for inputs in the disc of radius $2^p$ its in-box outputs lie in the disc and are within $\varepsilon_F$ of $2^p\mathcal F_t(2^{-p}U)$. Let $u,v$ be integer arrays with $|u_x|,|v_x|<2^b$, $b\le p$.
--
--   The algorithm `exactConv` scales $u,v$ to fixed point and applies $\widetilde{\mathcal F}_s=\tilde B\circ F_t\circ\tilde A$ (Gaussian resampling, Theorem 4.1) to both. It multiplies the results pointwise, applies $\widetilde{\mathcal F}_s$ to the conjugate, and rescales by $S^2\,2^{2b+6d\alpha^2}/2^p$ ($S=\prod_is_i$) with rounding to the nearest integer. Put $E=\varepsilon_A+\varepsilon_F+\varepsilon_B$, where $\varepsilon_A=d(6\lceil\sqrt p\rceil\alpha+4)$ and $\varepsilon_B=\sum_i(n_i(10m+12)+4)$ are the errors of Theorem 4.1. If
--   $$2\,(3E+2)\,S^2\,2^{2b+6d\alpha^2}<2^p,$$
--   then at every index of the box $\prod_i[0,s_i)$ the output equals the exact cyclic convolution
--   $$(u*v)_j=\sum_{k}u_k\,v_{j-k\bmod s}.$$
--   This is the correctness half of the recursive step of Harvey–van der Hoeven (Proposition 5.4), with the power-of-two transform left as a hypothesis. It can be discharged by Theorem 3.1 or by Bluestein's reduction (`bluestein_fp`) to any convolution routine.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, §5.3 (proof of Proposition 5.4)

import Definitions.Def_IntMul_HvdH_ExactConv

namespace IntMul.HvdH
theorem exactConv_eq {d : ℕ} (p α b : ℕ) (s t : Fin d → ℕ) [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]
    (hst : ∀ i, s i < t i) (hcop : ∀ i, Nat.Coprime (s i) (t i))
    (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hx : ∀ i, s i ≤ α ^ 2 * (t i - s i))
    (hp : ∀ i, 100 * (jIter p (s i) (t i) α * (10 * eWidth p α + 12) + 1) ≤ 2 ^ p)
    (hpA : 4 * (6 * sWidth p α + 4) ≤ 2 ^ p)
    (Ft : ((Fin d → ℕ) → ℤ × ℤ) → ((Fin d → ℕ) → ℤ × ℤ)) (εF : ℝ)
    (hFt : ∀ U : (Fin d → ℕ) → ℤ × ℤ, InDisc p U → ∀ j : Fin d → ℕ, (∀ i, j i < t i) →
      ‖gC (Ft U j)‖ ≤ 2 ^ p ∧
      ‖gC (Ft U j) - 2 ^ p * dftBox t (fun x => gC (U x) / 2 ^ p) j‖ ≤ εF)
    (hb : b ≤ p) (u v : (Fin d → ℕ) → ℤ) (hu : ∀ x, |u x| < 2 ^ b) (hv : ∀ x, |v x| < 2 ^ b)
    (hprec : 2 * (3 * ((∑ _i : Fin d, (6 * sWidth p α + 4 : ℝ)) + εF +
        ∑ i, ((jIter p (s i) (t i) α : ℝ) * (10 * eWidth p α + 12) + 4)) + 2) *
        ((∏ i, s i : ℕ) : ℝ) ^ 2 * 2 ^ (2 * b + 6 * d * α ^ 2) < 2 ^ p) :
    ∀ j : Fin d → ℕ, (∀ i, j i < s i) → exactConv p α b s t Ft u v j = convBox s u v j := by sorry
end IntMul.HvdH
