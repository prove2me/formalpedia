-- Prove2me | Theorems.Thm_MultiChoiceSecretary_Alg_binomial_min_bound
-- name    : MultiChoiceSecretary.Alg.binomial_min_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:25.509992+00:00
-- url     : https://prove2.me/theorems/7e73c0d4-f30c-4a73-ab17-3ae9bd3cb8d1
-- title:
--   Proof sketch of Theorem 2.1, PDF p. 2 — Σ_r Pr(|Y∩T| = r)·(min(r, ℓ)/k)v ≥ (1 − 1/(2√k))·v/2, ℓ = k/2
-- statement:
--   For every integer $k \ge 1$ and every real $v \ge 0$, with $\ell = k/2$,
--
--   $$\sum_{r=1}^{k} \binom{k}{r}2^{-k}\cdot\frac{\min(r,\ell)}{k}\,v \;\ge\; \Big(1 - \frac{1}{2\sqrt k}\Big)\frac{v}{2}.$$
--
--   This is the displayed inequality of the "third consequence" in the proof sketch of Theorem 2.1, with $\Pr(|Y\cap T| = r)$ replaced by its value $\binom{k}{r}2^{-k}$ (the binomial law of $|Y \cap T|$). It lower-bounds the expected modified value of the top $\ell$ elements of $Y$.
--
--   **Formalization Note.** $\ell$ is the real number $k/2$, as printed in the sketch ("$\ell = k/2$"). With $\ell = \lfloor k/2\rfloor$ the inequality fails for odd $k$ (for $k = 3$ the sum is $0.2917\,v$ against $0.3557\,v$).
-- source:
--   Kleinberg, A multiple-choice secretary algorithm with applications to online auctions, SODA 2005, PDF p. 2, proof sketch of Theorem 2.1, "Third, …" display Σ_{r=1}^{k} Pr(|Y ∩ T| = r)·(min(r, ℓ)/k)v ≥ (1 − 1/(2√k)) v/2

import Mathlib
import Definitions.Def_MultiChoiceSecretary_Alg_Setting

namespace MultiChoiceSecretary.Alg

theorem binomial_min_bound (k : ℕ) (hk : 1 ≤ k) (v : ℝ) (hv : 0 ≤ v) :
    (1 - 1 / (2 * Real.sqrt k)) * (v / 2) ≤
      ∑ r ∈ Finset.Icc 1 k, (k.choose r : ℝ) / 2 ^ k * (min (r : ℝ) ((k : ℝ) / 2) / k * v) := by sorry

end MultiChoiceSecretary.Alg
