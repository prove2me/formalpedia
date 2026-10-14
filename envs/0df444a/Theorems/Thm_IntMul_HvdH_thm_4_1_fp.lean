-- Prove2me | Theorems.Thm_IntMul_HvdH_thm_4_1_fp
-- name    : IntMul.HvdH.thm_4_1_fp
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T01:23:08.731979+00:00
-- url     : https://prove2.me/theorems/bc98f505-a107-4ae8-a745-b7a1d07b9bf7
-- title:
--   Multidimensional Gaussian resampling as fixed-point approximations (Theorem 4.1)
-- statement:
--   Let $d\ge0$. For each $i<d$ let $s_i<t_i$ be coprime positive integers with $s_i\le\alpha^2(t_i-s_i)$, i.e. $\alpha^2\theta_i\ge1$. Let $\alpha\ge2$ with $\alpha^2\le p$, and assume the precision conditions of `prop_4_7_fp` for each $i$.
--
--   Then there are linear maps $\mathcal A_i:\mathbb C^{s_i}\to\mathbb C^{t_i}$ and $\mathcal B_i:\mathbb C^{t_i}\to\mathbb C^{s_i}$ with the following properties.
--   * $\|\mathcal A_i\|,\|\mathcal B_i\|\le1$ and $F_{s_i}=2^{2\alpha^2}\mathcal B_iF_{t_i}\mathcal A_i$. Hence $F_{s_1,\dots,s_d}=2^{2d\alpha^2}\mathcal BF_{t_1,\dots,t_d}\mathcal A$ with $\mathcal A=\bigotimes_i\mathcal A_i$ and $\mathcal B=\bigotimes_i\mathcal B_i$.
--   * The slice-by-slice fixed-point maps $\tilde{\mathcal A}=\bigotimes_i$`Sapprox` and $\tilde{\mathcal B}=\bigotimes_i$`Bapprox` (`tensorMapZ`) are numerical approximations of $\mathcal A$ and $\mathcal B$ (`FPApprox`). Their errors are $\sum_i(6\lceil\sqrt p\rceil\alpha+4)$ and $\sum_i(n_i(10m+12)+4)$.
--   * $\mathcal A$ and $\mathcal B$ are $1$-Lipschitz for the sup norm.
--
--   This is Theorem 4.1 of Harvey–van der Hoeven, deduced from Proposition 4.7 (`prop_4_7_fp`) and Lemma 2.11 (`fp_tensor`).
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Theorem 4.1

import Theorems.Thm_IntMul_HvdH_prop_4_7_fp
import Theorems.Thm_IntMul_HvdH_fp_tensor
import Theorems.Thm_IntMul_HvdH_lip_tensor

namespace IntMul.HvdH
theorem thm_4_1_fp {d : ℕ} (p α : ℕ) (s t : Fin d → ℕ) [∀ i, NeZero (s i)] [∀ i, NeZero (t i)]
    (hst : ∀ i, s i < t i) (hcop : ∀ i, Nat.Coprime (s i) (t i))
    (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hx : ∀ i, s i ≤ α ^ 2 * (t i - s i))
    (hp : ∀ i, 100 * (jIter p (s i) (t i) α * (10 * eWidth p α + 12) + 1) ≤ 2 ^ p)
    (hpA : 4 * (6 * sWidth p α + 4) ≤ 2 ^ p) :
    ∃ (A : ∀ i, (ZMod (s i) → ℂ) →L[ℂ] (ZMod (t i) → ℂ))
      (B : ∀ i, (ZMod (t i) → ℂ) →L[ℂ] (ZMod (s i) → ℂ)),
      (∀ i, ‖A i‖ ≤ 1 ∧ ‖B i‖ ≤ 1 ∧ ∀ u, (s i : ℂ)⁻¹ • ZMod.dft u =
        (2 : ℂ) ^ (2 * α ^ 2) • B i ((t i : ℂ)⁻¹ • ZMod.dft (A i u))) ∧
      FPApprox p (tensorMapZ fun i => Sapprox p (s i) (t i) α)
        (tensorMap fun i (x : ℕ → ℂ) (k : ℕ) => A i (fun j => x j.val) (k : ZMod (t i)))
        (∑ _i : Fin d, (6 * sWidth p α + 4 : ℝ)) ∧
      FPApprox p (tensorMapZ fun i => Bapprox p (s i) (t i) α)
        (tensorMap fun i (x : ℕ → ℂ) (j : ℕ) => B i (fun k => x k.val) (j : ZMod (s i)))
        (∑ i, ((jIter p (s i) (t i) α : ℝ) * (10 * eWidth p α + 12) + 4)) ∧
      SupLip (tensorMap fun i (x : ℕ → ℂ) (k : ℕ) => A i (fun j => x j.val) (k : ZMod (t i))) ∧
      SupLip (tensorMap fun i (x : ℕ → ℂ) (j : ℕ) => B i (fun k => x k.val) (j : ZMod (s i))) := by sorry
end IntMul.HvdH
