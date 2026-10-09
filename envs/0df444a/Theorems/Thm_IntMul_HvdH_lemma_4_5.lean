-- Prove2me | Theorems.Thm_IntMul_HvdH_lemma_4_5
-- name    : IntMul.HvdH.lemma_4_5
-- status  : Proved
-- author  : @avi
-- created : 2026-10-08T17:34:28.766719+00:00
-- url     : https://prove2.me/theorems/9ef112bf-8d24-4b25-999a-bec3d80c1b8f
-- title:
--   Lemma 4.5 — $\|\mathcal S\|<1+\alpha^{-1}$
-- statement:
--   Let $s$ and $t>s$ be positive integers with $\gcd(s,t)=1$, and let $\alpha>0$. The resampling map $\mathcal S:\mathbb C^s\to\mathbb C^t$,
--   $$(\mathcal Su)_k=\alpha^{-1}\sum_{j\in\mathbb Z}e^{-\pi\alpha^{-2}s^2(k/t-j/s)^2}u_{j\bmod s},$$
--   satisfies
--   $$\|\mathcal S\|<1+\alpha^{-1},$$
--   where $\|\cdot\|$ is the operator norm with respect to the supremum norms on $\mathbb C^s$ and $\mathbb C^t$.
--
--   This bound keeps the forward resampling step numerically stable, with growth by at most a constant factor.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Annals of Mathematics 193(2) (2021) 563-617, https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), §4.1, Lemma 4.5, p. 26 (setting of §4.1; norms of §2.2, §2.6)

import Mathlib
import Definitions.Def_IntMul_HvdH_Resampling

namespace IntMul.HvdH

theorem lemma_4_5 (s t : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hcop : Nat.Coprime s t)
    (α : ℝ) (hα : 0 < α) :
    ‖resS s t α‖ < 1 + α⁻¹ := by sorry

end IntMul.HvdH
