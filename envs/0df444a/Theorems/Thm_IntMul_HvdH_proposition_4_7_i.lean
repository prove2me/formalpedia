-- Prove2me | Theorems.Thm_IntMul_HvdH_proposition_4_7_i
-- name    : IntMul.HvdH.proposition_4_7_i
-- status  : Proved
-- author  : @avi
-- created : 2026-10-09T01:44:27.28793+00:00
-- url     : https://prove2.me/theorems/10d16c64-499c-4de9-bae1-165e2c3d6ee0
-- title:
--   HvdH Proposition 4.7(i) — one-dimensional Gaussian resampling $\mathcal F_s=2^{2\alpha^2}\mathcal B\mathcal F_t\mathcal A$
-- statement:
--   Let $p\ge100$ (the working precision) and let $s,t$ be integers with $2\le s<t<2^p$ and $\gcd(s,t)=1$. Let $\alpha$ be an integer with $2\le\alpha<p^{1/2}$, put $\theta:=t/s-1$, and assume $\theta\ge p/\alpha^4$. Then there exist $\mathbb C$-linear maps $\mathcal A:\mathbb C^s\to\mathbb C^t$ and $\mathcal B:\mathbb C^t\to\mathbb C^s$ with $\|\mathcal A\|,\|\mathcal B\|\le1$ such that
--   $$\mathcal F_s \;=\; 2^{2\alpha^2}\,\mathcal B\,\mathcal F_t\,\mathcal A .$$
--
--   Here $\mathcal F_n$ is the normalised DFT $(\mathcal F_nu)_j=\frac1n\sum_ke^{-2\pi ijk/n}u_k$ and norms are operator norms for the supremum norm. In the paper $\mathcal A=\mathcal S/2$ and $\mathcal B=\mathcal P_s^{-1}\mathcal D'\mathcal J'\mathcal C\mathcal P_t$, built from the maps of §4.1–4.2; the proof combines Theorem 4.2, Lemma 4.5 and Lemma 4.6 (all on the platform). Part (ii) of the proposition (fast numerical approximations of $\mathcal A,\mathcal B$) is a statement about Turing-machine costs and is not part of this theorem.
--
--   Formalization note: `dft` and `theta` are from `IntMul_HvdH_Resampling`.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), Proposition 4.7, part (i), p. 29 (precision p ≥ 100 from §2.2, p. 8).

import Mathlib
import Definitions.Def_IntMul_HvdH_Resampling

namespace IntMul.HvdH

theorem proposition_4_7_i (p s t : ℕ) [NeZero s] [NeZero t] (hp : 100 ≤ p) (hs : 2 ≤ s)
    (hst : s < t) (htp : t < 2 ^ p) (hcop : Nat.Coprime s t) (α : ℕ) (hα : 2 ≤ α)
    (hαp : (α : ℝ) < Real.sqrt p) (hθ : (p : ℝ) / α ^ 4 ≤ theta s t) :
    ∃ A : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ), ∃ B : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ dft s = ((2 : ℂ) ^ (2 * α ^ 2)) • (B.comp ((dft t).comp A)) := by sorry

end IntMul.HvdH
