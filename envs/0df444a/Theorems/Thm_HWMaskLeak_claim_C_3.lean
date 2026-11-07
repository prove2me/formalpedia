-- Prove2me | Theorems.Thm_HWMaskLeak_claim_C_3
-- name    : HWMaskLeak.claim_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:31:15.648191+00:00
-- url     : https://prove2.me/theorems/e40533be-17b5-435a-804f-507d47ed903a
-- title:
--   Claim C.3 — Gaussian-type and near-$\pi$ bounds for $L_p$
-- statement:
--   1. For real $\varepsilon_0$ and $\varepsilon_0\le p\le1-\varepsilon_0$, and every $\varphi\in\mathbb R$,
--   $$
--   L_p(\varphi)\le\exp\bigl(-2\varepsilon_0(1-\varepsilon_0)\sin^2(\varphi/2)\bigr);
--   $$
--   in particular, for $\varepsilon_0=1/3$, $L_p(\varphi)\le\exp\bigl(-\tfrac49\sin^2(\varphi/2)\bigr)$.
--   2. If the distance between $\pi$ and $\varphi+2\pi\mathbb Z$ is at most $\varepsilon$, then for every $p\in[0,1]$,
--   $$
--   L_p(\varphi)\le|1-2p|+\varepsilon.
--   $$
--
--   Part 1 gives the Gaussian decay of the long factor groups in Lemma 4.11; part 2 bounds a factor whose angle is near $\pi$.
--
--   Differences from the source:
--   - encoding: the distance between π and φ + 2πℤ is ≤ ε → ∃ k : ℤ, |φ − (2k + 1)π| ≤ ε; reason: the distance to the discrete set π + 2πℤ is attained at some point (2k+1)π
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), App. C.5, Claim C.3, p.49

import Mathlib
import Definitions.Def_HWMaskLeak_Lp

namespace HWMaskLeak

/-- **Claim C.3** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), App. C.5, Claim C.3, p.49): for `ε₀ ⩽ p ⩽ 1 − ε₀` and every `φ ∈ ℝ`,
1. `L_p(φ) ⩽ exp(−2ε₀(1 − ε₀) sin²(φ/2))`; in particular, when `ε₀ = 1/3`,
   `L_p(φ) ⩽ exp(−(4/9) sin²(φ/2))`;
2. if the distance between `π` and `φ + 2πℤ` is `⩽ ε`, then for every `p ∈ [0, 1]`,
   `L_p(φ) ⩽ |1 − 2p| + ε`.

**Formalization Note** Part 1 is stated for every real `ε₀`. "The distance between `π` and
`φ + 2πℤ` is `⩽ ε`" is `∃ k : ℤ, |φ − (2k + 1)π| ⩽ ε`. -/
theorem claim_C_3 :
    (∀ ε₀ p φ : ℝ, ε₀ ≤ p → p ≤ 1 - ε₀ →
      Lp p φ ≤ Real.exp (-(2 * ε₀ * (1 - ε₀)) * Real.sin (φ / 2) ^ 2)) ∧
    (∀ p φ : ℝ, 1 / 3 ≤ p → p ≤ 1 - 1 / 3 →
      Lp p φ ≤ Real.exp (-(4 / 9) * Real.sin (φ / 2) ^ 2)) ∧
    (∀ p φ ε : ℝ, 0 ≤ p → p ≤ 1 → (∃ k : ℤ, |φ - (2 * k + 1) * Real.pi| ≤ ε) →
      Lp p φ ≤ |1 - 2 * p| + ε) := by sorry

end HWMaskLeak
