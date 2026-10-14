-- Prove2me | Theorems.Thm_IntMul_HvdH_prop_4_7_fp
-- name    : IntMul.HvdH.prop_4_7_fp
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T01:09:16.98784+00:00
-- url     : https://prove2.me/theorems/33d42821-080d-4ff2-80c9-72d487cf91d8
-- title:
--   Gaussian resampling in one dimension as fixed-point approximations (Proposition 4.7)
-- statement:
--   Let $s<t$ be coprime positive integers. Let $\alpha\ge2$ and $p$ be integers with $\alpha^2\le p$ and $\alpha^2\theta\ge1$, where $\theta=t/s-1$, i.e. $s\le\alpha^2(t-s)$. Let $n$ = `jIter p s t α`, $m$ = `eWidth p α` and $m'$ = `sWidth p α`, and assume $100(n(10m+12)+1)\le2^p$ and $4(6m'+4)\le2^p$.
--
--   Then there are linear maps $\mathcal A:\mathbb C^s\to\mathbb C^t$ and $\mathcal B:\mathbb C^t\to\mathbb C^s$ with the following properties.
--   * $\|\mathcal A\|,\|\mathcal B\|\le1$.
--   * $$F_s=2^{2\alpha^2}\mathcal BF_t\mathcal A.$$
--   * `Sapprox` and `Bapprox` are numerical approximations of $\mathcal A$ and $\mathcal B$ in the sense of `FPApprox` (`IntMul_HvdH_FPApprox`), with errors $6m'+4$ and $n(10m+12)+4$. In particular they map the unit polydisc to itself.
--
--   Here vectors in $\mathbb C^n$ are stored as $\mathbb N$-indexed arrays read modulo $n$. The lifted maps are $1$-Lipschitz for the sup norm, so they can be composed with `fp_comp` and tensored with `fp_tensor`. This is Proposition 4.7 of Harvey–van der Hoeven. The proof uses the sharper bounds $\|\mathcal A\|\le0.55$ (Lemma 4.5 via Poisson summation) and $\|\mathcal B\|\le1/2$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Proposition 4.7

import Mathlib
import Definitions.Def_IntMul_HvdH_BApprox
import Definitions.Def_IntMul_HvdH_FPApprox
import Theorems.Thm_IntMul_HvdH_Sapprox_bound
import Theorems.Thm_IntMul_HvdH_Dapprox_bound
import Theorems.Thm_IntMul_HvdH_Japprox_bound

namespace IntMul.HvdH
theorem prop_4_7_fp (p s t α : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
    (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p) (hx : s ≤ α ^ 2 * (t - s))
    (hp : 100 * (jIter p s t α * (10 * eWidth p α + 12) + 1) ≤ 2 ^ p)
    (hpA : 4 * (6 * sWidth p α + 4) ≤ 2 ^ p) :
    ∃ (A : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ)) (B : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ)),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
      (∀ u, (s : ℂ)⁻¹ • ZMod.dft u = (2 : ℂ) ^ (2 * α ^ 2) • B ((t : ℂ)⁻¹ • ZMod.dft (A u))) ∧
      FPApprox p (Sapprox p s t α) (fun (x : ℕ → ℂ) (k : ℕ) => A (fun j => x j.val) (k : ZMod t))
        (6 * sWidth p α + 4) ∧
      FPApprox p (Bapprox p s t α) (fun (x : ℕ → ℂ) (j : ℕ) => B (fun k => x k.val) (j : ZMod s))
        (jIter p s t α * (10 * eWidth p α + 12) + 4) ∧
      SupLip (fun (x : ℕ → ℂ) (k : ℕ) => A (fun j => x j.val) (k : ZMod t)) ∧
      SupLip (fun (x : ℕ → ℂ) (j : ℕ) => B (fun k => x k.val) (j : ZMod s)) := by sorry
end IntMul.HvdH
