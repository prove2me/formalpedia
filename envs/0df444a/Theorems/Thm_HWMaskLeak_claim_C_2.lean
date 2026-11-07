-- Prove2me | Theorems.Thm_HWMaskLeak_claim_C_2
-- name    : HWMaskLeak.claim_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:31:16.836351+00:00
-- url     : https://prove2.me/theorems/8ad6c968-671a-4e90-8da7-868c13e65bb4
-- title:
--   Claim C.2 — $\prod_{u<v}L_p(\theta+2\pi\{2^ux\})\ll|1-2p|+|\theta|+2^{-v}$
-- statement:
--   There is an absolute constant $C$ such that for every $p\in[0,1]$, every integer $v\ge1$, every $x\in[1/4,3/4]$ and every $\theta\in\mathbb R$,
--   $$
--   \prod_{u=0}^{v-1}L_p\bigl(\theta+2\pi\{2^ux\}\bigr)\le C\bigl(|1-2p|+|\theta|+2^{-v}\bigr).
--   $$
--
--   It handles the case of Claim C.1 in which the orbit $\{2^jt/N\}$ enters $(1/4,1/2]$ early enough to fit a whole block of $\lceil\frac12\log_2n\rceil$ indices.
--
--   Differences from the source:
--   - encoding: the product ≪ … (implied absolute constant) → ∃ C : ℝ, chosen before every other variable; reason: the paper's ≪ hides an absolute constant independent of n, N and the other parameters (§2.1, p.16)
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), App. C.4, Claim C.2, p.47

import Mathlib
import Definitions.Def_HWMaskLeak_Lp

namespace HWMaskLeak

/-- **Claim C.2** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), App. C.4, Claim C.2, p.47): for every `p ∈ [0, 1]`, integer `v ⩾ 1`,
`x ∈ [1/4, 3/4]` and `θ ∈ ℝ`, `Π_{u=0}^{v−1} L_p(θ + 2π{2ᵘx}) ≪ |1 − 2p| + |θ| + 2^{−v}`.

**Formalization Note** `≪` is an absolute constant `C`, chosen before `p, v, x, θ`; `{·}` is
`Int.fract`. -/
theorem claim_C_2 :
    ∃ C : ℝ, ∀ p : ℝ, 0 ≤ p → p ≤ 1 → ∀ v : ℕ, 1 ≤ v → ∀ x : ℝ, 1 / 4 ≤ x → x ≤ 3 / 4 →
      ∀ θ : ℝ,
        ∏ u ∈ Finset.range v, Lp p (θ + 2 * Real.pi * Int.fract ((2 : ℝ) ^ u * x)) ≤
          C * (|1 - 2 * p| + |θ| + ((2 : ℝ) ^ v)⁻¹) := by sorry

end HWMaskLeak
