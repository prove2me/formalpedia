-- Prove2me | Theorems.Thm_HWMaskLeak_lemma_4_4
-- name    : HWMaskLeak.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:07.672281+00:00
-- url     : https://prove2.me/theorems/95d2e557-f324-4eb2-a7c7-1ee3b10d54f7
-- title:
--   Lemma 4.4 — one-share model contraction
-- statement:
--   Let $Q:=2^n$ and $N\ge2$. For every integer $m\ge2$,
--   $$
--   F^{\mathrm{bin}}_m(N)\le\Bigl(\frac QN\Bigr)^{1/2}\alpha_{\mathrm{bin}}(N)^{1/2}F^{\mathrm{bin}}_{m-1}(N),
--   $$
--   where $\alpha_{\mathrm{bin}}(N)=\max_{t\ne0}\sum_{w\in W_{\mathrm{bin}}}|\hat B_w(t)|^2/\rho_w(N)$ and $\rho_w(N)=\frac1N\binom nw$.
--
--   Together with $\alpha_{\mathrm{bin}}(N)\ll1/n$ (Lemma 4.5) each additional share gains a factor $n^{-1/2}$.
--
--   Differences from the source:
--   - generalization: under the standing window |N − 2ⁿ| ≤ 2ⁿ/n of §4 → every n and every N ≥ 2; reason: the proof (App. C.2, Claim B.3 with Σ_w ρ_w(N) = Q/N) uses no window; within the window with n ≥ 3 one has N ≥ 6, so the statement specializes to the source's
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), Lemma 4.4, p.21

import Mathlib
import Definitions.Def_HWMaskLeak_energyBin
import Definitions.Def_HWMaskLeak_alphaBin

namespace HWMaskLeak

/-- **Lemma 4.4 (One-share model contraction)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), Lemma 4.4, p.21): with `Q := 2ⁿ`, for every
integer `m ⩾ 2`, `F^bin_m(N) ⩽ (Q/N)^{1/2} · α_bin(N)^{1/2} · F^bin_{m−1}(N)`.

**Formalization Note** Stated for every `n` and every `N ⩾ 2`, without the window of §4; the square
roots are `Real.sqrt` (`α_bin(N) ⩾ 0`). -/
theorem lemma_4_4 (n N : ℕ) [NeZero N] (hN : 2 ≤ N) (m : ℕ) (hm : 2 ≤ m) :
    energyBin n N m ≤
      Real.sqrt ((2 : ℝ) ^ n / N) * Real.sqrt (alphaBin n N) * energyBin n N (m - 1) := by sorry

end HWMaskLeak
