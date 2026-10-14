-- Prove2me | Theorems.Thm_IntMul_HvdH_Eapprox_bound
-- name    : IntMul.HvdH.Eapprox_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T00:01:37.039331+00:00
-- url     : https://prove2.me/theorems/d6dc96b1-7793-441a-a7e5-4eb0de38af4a
-- title:
--   Truncated approximation of the off-diagonal map $\mathcal E$ (Lemma 4.11)
-- statement:
--   Let $p,s,t,\alpha,\ell$ be integers with $1\le s\le t$ and $\alpha\ge1$. Let $U_i\in\mathbb Z[i]$ with $|U_i|\le2^p$, so that $u_i=2^{-p}U_i$ lies in the unit disc. Let $m=\lceil\lceil\sqrt p\rceil/\alpha\rceil+1$. Then the output $Z_\ell$ of `Eapprox` (see `IntMul_HvdH_EApprox`) satisfies
--   $$\bigl|Z_\ell-2^p(\mathcal Eu)_\ell\bigr|\le5m+5,$$
--   that is, $\varepsilon(\tilde{\mathcal E}u)\le5m+5=O(p^{1/2}/\alpha+1)$.
--
--   This is Lemma 4.11 of Harvey–van der Hoeven, where the bound is $8m+3<\tfrac13p$. The proof uses $(th+b_\ell)^2-b_{\ell+h}^2\ge s^2|h|(|h|-1)$ for $h\ne0$ to bound the tail $|h|>m$ by $2\cdot2^{-p}$, and Lemma 2.13 with rounding for each of the $2m$ remaining terms.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 4.11

import Definitions.Def_IntMul_HvdH_EApprox
import Theorems.Thm_IntMul_HvdH_expNeg_bound

namespace IntMul.HvdH
theorem Eapprox_bound (p s t α l : ℕ) (hs : 0 < s) (hst : s ≤ t) (hα : 1 ≤ α)
    (U : ℕ → ℤ × ℤ) (hU : ∀ i, ‖((U i).1 : ℂ) + ((U i).2 : ℂ) * Complex.I‖ ≤ 2 ^ p) :
    ‖(((Eapprox p s t α U l).1 : ℂ) + ((Eapprox p s t α U l).2 : ℂ) * Complex.I) -
      2 ^ p * Eexact s t α (fun i => (((U i).1 : ℂ) + ((U i).2 : ℂ) * Complex.I) / 2 ^ p) l‖
      ≤ 5 * eWidth p α + 5 := by sorry
end IntMul.HvdH
