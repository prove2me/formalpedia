-- Prove2me | Theorems.Thm_IntMul_HvdH_theorem_4_1_i
-- name    : IntMul.HvdH.theorem_4_1_i
-- status  : Proved
-- author  : @avi
-- created : 2026-10-09T01:44:41.040266+00:00
-- url     : https://prove2.me/theorems/903110fa-eef6-4ade-94e6-b12de92324ea
-- title:
--   HvdH Theorem 4.1 (first part) — Gaussian resampling $\mathcal F_{s_1,\dots,s_d}=2^{\gamma}\mathcal B\mathcal F_{t_1,\dots,t_d}\mathcal A$
-- statement:
--   Let $d\ge1$ and $p\ge100$. Let $s_1,\dots,s_d$ and $t_1,\dots,t_d$ be integers with $2\le s_i<t_i<2^p$ and $\gcd(s_i,t_i)=1$. Let $\alpha$ be an integer with $2\le\alpha<p^{1/2}$, put $\theta_i:=t_i/s_i-1$, and assume $\theta_i\ge p/\alpha^4$ for every $i$. Then there exist $\mathbb C$-linear maps $\mathcal A:\bigotimes_i\mathbb C^{s_i}\to\bigotimes_i\mathbb C^{t_i}$ and $\mathcal B:\bigotimes_i\mathbb C^{t_i}\to\bigotimes_i\mathbb C^{s_i}$ with $\|\mathcal A\|,\|\mathcal B\|\le1$ such that
--   $$\mathcal F_{s_1,\dots,s_d}\;=\;2^{\gamma}\,\mathcal B\,\mathcal F_{t_1,\dots,t_d}\,\mathcal A,\qquad\gamma:=2d\alpha^2 .$$
--
--   In the paper $\mathcal A,\mathcal B$ are tensor products of the one-dimensional maps of Proposition 4.7(i). The theorem's second assertion (numerical approximations and their cost) concerns Turing-machine costs and is not part of this statement.
--
--   Formalization note: arrays are functions on $\prod_i\mathbb Z/n_i\mathbb Z$ with the supremum norm; $\mathcal F_{n_1,\dots,n_d}$ is `dftN` from `IntMul_HvdH_Tensor` and $\theta$ is `theta` from `IntMul_HvdH_Resampling`.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), Theorem 4.1, first assertion, p. 23 (precision p ≥ 100 from §2.2, p. 8).

import Mathlib
import Definitions.Def_IntMul_HvdH_Resampling
import Definitions.Def_IntMul_HvdH_Tensor

namespace IntMul.HvdH

theorem theorem_4_1_i (d p : ℕ) (hd : 1 ≤ d) (hp : 100 ≤ p) (s t : Fin d → ℕ)
    [∀ i, NeZero (s i)] [∀ i, NeZero (t i)] (hs : ∀ i, 2 ≤ s i) (hst : ∀ i, s i < t i)
    (htp : ∀ i, t i < 2 ^ p) (hcop : ∀ i, Nat.Coprime (s i) (t i)) (α : ℕ) (hα : 2 ≤ α)
    (hαp : (α : ℝ) < Real.sqrt p) (hθ : ∀ i, (p : ℝ) / α ^ 4 ≤ theta (s i) (t i)) :
    ∃ A : (TIdx s → ℂ) →L[ℂ] (TIdx t → ℂ), ∃ B : (TIdx t → ℂ) →L[ℂ] (TIdx s → ℂ),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧
        dftN s = ((2 : ℂ) ^ (2 * d * α ^ 2)) • (B.comp ((dftN t).comp A)) := by sorry

end IntMul.HvdH
