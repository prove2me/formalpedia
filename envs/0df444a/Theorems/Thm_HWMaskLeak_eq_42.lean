-- Prove2me | Theorems.Thm_HWMaskLeak_eq_42
-- name    : HWMaskLeak.eq_42
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:59.085398+00:00
-- url     : https://prove2.me/theorems/fe53bacb-2cb3-4899-8520-7c67728a203f
-- title:
--   Eq. (42) — $2\Delta^{\mathrm{bin}}_m(N)\le F^{\mathrm{bin}}_m(N)$
-- statement:
--   For every $n$, every $N\ge1$ and every $m\ge1$,
--   $$
--   2\Delta^{\mathrm{bin}}_m(N)=\sum_{w\in W^m}\frac1N\sum_{x\in G}\Bigl|\sum_{t\ne0}e_N(xt)\prod_{j=1}^m\hat B_{w_j}(t)\Bigr|\le\sum_{w\in W^m}\sqrt{\sum_{t\ne0}\prod_{j=1}^m|\hat B_{w_j}(t)|^2}=F^{\mathrm{bin}}_m(N),
--   $$
--   with $W=W_{\mathrm{bin}}=\{0,\dots,n\}$.
--
--   This is the full-range analogue of $2\Delta_{k-1}\le F_{k-1}$ and drives the second part of Corollary 4.
--
--   Differences from the source:
--   - generalization: under the standing window |N − 2ⁿ| ≤ 2ⁿ/n of §4 and App. D → every n and every N ≥ 1; reason: the proof (Claim B.1 with f_x = 1_{−x}) uses no window; it specializes to the source's range
--   - encoding: the two outer equalities of (42) → the inequality 2·maskSumDistBin ≤ energyBin; reason: the equalities are the definitions (39) and (22)
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), App. D.2, p.53, eq. (42)

import Mathlib
import Definitions.Def_HWMaskLeak_maskSumDistBin
import Definitions.Def_HWMaskLeak_energyBin

namespace HWMaskLeak

/-- **Eq. (42)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), App. D.2, eq. (42), p.53): for every `m ⩾ 1`,
`2Δ^bin_m(N) = Σ_{w ∈ W^m} (1/N) Σ_{x ∈ G} |Σ_{t≠0} e_N(xt) Π_j B̂_{w_j}(t)| ⩽
Σ_{w ∈ W^m} √(Σ_{t≠0} Π_j |B̂_{w_j}(t)|²) = F^bin_m(N)`, with `W = W_bin`.

**Formalization Note** The two equalities are the definitions (39) and (22); stated for every `n`
and every `N ⩾ 1`. -/
theorem eq_42 (n N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m) :
    2 * maskSumDistBin n N m ≤ energyBin n N m := by sorry

end HWMaskLeak
