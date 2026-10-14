-- Prove2me | Theorems.Thm_IntMul_HvdH_Sapprox_bound
-- name    : IntMul.HvdH.Sapprox_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T23:46:32.231986+00:00
-- url     : https://prove2.me/theorems/d17e08c6-11dd-4696-930a-7ef17cc93259
-- title:
--   Truncated approximation of the resampling map $\mathcal S'$ (Lemma 4.9)
-- statement:
--   Let $p,s,t,\alpha,k$ be integers with $s,t\ge1$, $\alpha\ge2$ and $\alpha^2\le p$. Let $U_i\in\mathbb Z[i]$ with $|U_i|\le2^p$, so that $u_i=2^{-p}U_i$ lies in the unit disc. Let $m=\lceil\sqrt p\rceil\alpha$. Then the output $Z_k$ of `Sapprox` (see `IntMul_HvdH_SApprox`) satisfies
--   $$\bigl|Z_k-2^p(\mathcal S'u)_k\bigr|\le6m+4,$$
--   that is, $\varepsilon(\tilde{\mathcal S}'u)\le6m+4=O(p)$. This is Lemma 4.9 of Harvey–van der Hoeven, where the bound is $14m+1<16p$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 4.9

import Definitions.Def_IntMul_HvdH_SApprox
import Theorems.Thm_IntMul_HvdH_expNeg_bound

namespace IntMul.HvdH
theorem Sapprox_bound (p s t α k : ℕ) (hs : 0 < s) (ht : 0 < t) (hα : 2 ≤ α) (hαp : α ^ 2 ≤ p)
    (U : ℕ → ℤ × ℤ) (hU : ∀ i, ‖((U i).1 : ℂ) + ((U i).2 : ℂ) * Complex.I‖ ≤ 2 ^ p) :
    ‖(((Sapprox p s t α U k).1 : ℂ) + ((Sapprox p s t α U k).2 : ℂ) * Complex.I) -
      2 ^ p * Sexact s t α (fun i => (((U i).1 : ℂ) + ((U i).2 : ℂ) * Complex.I) / 2 ^ p) k‖
      ≤ 6 * sWidth p α + 4 := by sorry
end IntMul.HvdH
