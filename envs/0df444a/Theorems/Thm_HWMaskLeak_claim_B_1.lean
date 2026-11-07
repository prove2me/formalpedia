-- Prove2me | Theorems.Thm_HWMaskLeak_claim_B_1
-- name    : HWMaskLeak.claim_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:31:15.294869+00:00
-- url     : https://prove2.me/theorems/35ec082b-d652-4546-aff8-72ee9f7b12d9
-- title:
--   Claim B.1 — $L^2$ and $L^\infty$ bounds for sums of Fourier pairings
-- statement:
--   Let $N\ge1$, let $\Omega$ be a finite set, and for each $\omega\in\Omega$ let $f_\omega:\mathbb Z/N\mathbb Z\to\mathbb C$. For any complex numbers $(z_t:0<t<N)$,
--   $$
--   \sum_{\omega\in\Omega}\Bigl|\sum_{t\ne0}z_t\hat f_\omega(t)\Bigr|\le\Bigl\|\sum_{\omega\in\Omega}|f_\omega|\Bigr\|_{L^2}\sqrt{\sum_{t\ne0}|z_t|^2}\le\Bigl\|\sum_{\omega\in\Omega}|f_\omega|\Bigr\|_{L^\infty}\sqrt{\sum_{t\ne0}|z_t|^2},
--   $$
--   with the normalized norms $\|g\|_{L^2}=\bigl(\frac1N\sum_x|g(x)|^2\bigr)^{1/2}$ and $\|g\|_{L^\infty}=\max_x|g(x)|$.
--
--   Applied with $f_\omega$ the indicators of a partition of $G$, it gives $2\Delta_{k-1}\le F_{k-1}$ and the model inequality (42).
--
--   Differences from the source:
--   - encoding: complex numbers (z_t : 0 < t < N); a finite set Ω → a function z : ZMod N → ℂ whose value at 0 is unused; a Fintype index type; reason: only the values at t ≠ 0 enter both sides
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), App. B.1, Claim B.1, p.40

import Mathlib
import Definitions.Def_HWMaskLeak_fhat

namespace HWMaskLeak

/-- **Claim B.1** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), App. B.1, Claim B.1, p.40): let `Ω` be a finite set and `f_ω : ℤ/Nℤ → ℂ` for
`ω ∈ Ω`. For any complex numbers `(z_t : 0 < t < N)`,
`Σ_ω | Σ_{t≠0} z_t f̂_ω(t) | ⩽ ‖Σ_ω |f_ω|‖_{L²} √(Σ_{t≠0} |z_t|²) ⩽ ‖Σ_ω |f_ω|‖_{L∞} √(Σ_{t≠0} |z_t|²)`.

**Formalization Note** The norms are normalized as in (7), p.15:
`‖g‖_{L²} = ((1/N) Σ_x |g(x)|²)^{1/2}` and `‖g‖_{L∞} = max_x |g(x)|`. The family `z` is a function on
`ZMod N`; its value at `t = 0` does not enter. -/
theorem claim_B_1 (N : ℕ) [NeZero N] {ι : Type*} [Fintype ι] (f : ι → ZMod N → ℂ)
    (z : ZMod N → ℂ) :
    ∑ ω, ‖∑ t ∈ Finset.univ.filter (fun t : ZMod N => t ≠ 0), z t * fhat N (f ω) t‖ ≤
        Real.sqrt ((1 / (N : ℝ)) * ∑ x, (∑ ω, ‖f ω x‖) ^ 2) *
          Real.sqrt (∑ t ∈ Finset.univ.filter (fun t : ZMod N => t ≠ 0), ‖z t‖ ^ 2) ∧
      Real.sqrt ((1 / (N : ℝ)) * ∑ x, (∑ ω, ‖f ω x‖) ^ 2) *
          Real.sqrt (∑ t ∈ Finset.univ.filter (fun t : ZMod N => t ≠ 0), ‖z t‖ ^ 2) ≤
        Finset.univ.sup' Finset.univ_nonempty (fun x => ∑ ω, ‖f ω x‖) *
          Real.sqrt (∑ t ∈ Finset.univ.filter (fun t : ZMod N => t ≠ 0), ‖z t‖ ^ 2) := by sorry

end HWMaskLeak
