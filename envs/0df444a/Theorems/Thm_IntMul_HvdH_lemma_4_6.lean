-- Prove2me | Theorems.Thm_IntMul_HvdH_lemma_4_6
-- name    : IntMul.HvdH.lemma_4_6
-- status  : Proved
-- author  : @avi
-- created : 2026-10-08T17:35:36.786903+00:00
-- url     : https://prove2.me/theorems/bf25c0fa-3c74-4e21-ae08-b85763d9cdd6
-- title:
--   Lemma 4.6 — $\|\mathcal E\|<2.01\,e^{-\pi\alpha^2\theta/2}<2^{-\alpha^2\theta}$
-- statement:
--   Let $s$ and $t>s$ be positive integers with $\gcd(s,t)=1$, let $\alpha>0$, and put $\theta=t/s-1$. Let $[x]=\lfloor x+\tfrac12\rfloor$ and $\beta_\ell=t\ell/s-[t\ell/s]$. Define the maps:
--
--   1. the row-deleting map $\mathcal C:\mathbb C^t\to\mathbb C^s$, $(\mathcal Cu)_\ell=u_{[t\ell/s]}$;
--   2. the diagonal map $\mathcal D$, $(\mathcal Du)_\ell=e^{\pi\alpha^2\beta_\ell^2}u_\ell$;
--   3. $\mathcal N=\mathcal C\mathcal T\mathcal D$, where $\mathcal T$ is the resampling map of §4.1;
--   4. $\mathcal E=\mathcal N-\mathcal I$.
--
--   If $\alpha^2\theta\ge1$, then
--   $$\|\mathcal E\|<2.01\cdot e^{-\pi\alpha^2\theta/2}<2^{-\alpha^2\theta},$$
--   where $\|\cdot\|$ is the operator norm for the supremum norm on $\mathbb C^s$.
--
--   Consequently $\mathcal N=\mathcal I+\mathcal E$ is invertible by a rapidly converging Neumann series, and $\mathcal D\mathcal N^{-1}\mathcal C$ is an explicit left inverse of $\mathcal T$. This is how the resampling identity is inverted in Theorem 4.1.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Annals of Mathematics 193(2) (2021) 563-617, https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), §4.2, Lemma 4.6, p. 28 (setting of §4.1-4.2; theta = t/s - 1)

import Mathlib
import Definitions.Def_IntMul_HvdH_Resampling

namespace IntMul.HvdH

open Real

theorem lemma_4_6 (s t : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
    (α : ℝ) (hα : 0 < α) (hθ : 1 ≤ α ^ 2 * theta s t) :
    ‖errE s t α‖ < 2.01 * Real.exp (-π * α ^ 2 * theta s t / 2) ∧
      2.01 * Real.exp (-π * α ^ 2 * theta s t / 2) < (2 : ℝ) ^ (-(α ^ 2 * theta s t)) := by sorry

end IntMul.HvdH
