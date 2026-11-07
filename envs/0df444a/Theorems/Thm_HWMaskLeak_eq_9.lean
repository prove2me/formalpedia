-- Prove2me | Theorems.Thm_HWMaskLeak_eq_9
-- name    : HWMaskLeak.eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:31:52.09589+00:00
-- url     : https://prove2.me/theorems/c840609a-b51d-4781-8ffc-54022a0f1abe
-- title:
--   Eq. (9) — Fourier form of the insecurity $E_k(s)$
-- statement:
--   For every $N\ge1$, every $k\ge1$ and every secret $s\in G=\mathbb Z/N\mathbb Z$,
--   $$
--   E_k(s)=\frac12\sum_{w\in W^k}\Bigl|\sum_{t\in G,\,t\ne0}e_N(st)\prod_{j=1}^k\hat S_{w_j}(t)\Bigr|,
--   $$
--   where $W=\mathrm{wt}(G)$, $S_w$ is the weight-$w$ slice and $e_N(x)=\exp(2\pi\imath x/N)$.
--
--   The zero frequency of the Fourier inversion is exactly $D(U)(w)$, so the insecurity becomes a sum over nonzero frequencies; all Fourier-analytic bounds of the paper start from this identity.
--
--   Differences from the source:
--   - generalization: k-party sharing (k ≥ 2) → every k ≥ 1; reason: the identity also holds for k = 1, where it is Fourier inversion for one slice; it specializes to every k ≥ 2
--   - encoding: laws of uniform random shares, total variation distance → normalized counts on finite sets and ½ Σ |P − Q| over W^k (resp. W^m × G); reason: uniform choices on finite sets are counting measures; the summation range contains both supports, so no instance changes
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), §2.1, p.16, eq. (9)

import Mathlib
import Definitions.Def_HWMaskLeak_insecurity
import Definitions.Def_HWMaskLeak_fhat
import Definitions.Def_HWMaskLeak_slice

namespace HWMaskLeak

/-- **Eq. (9), the Fourier form of `E_k(s)`** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), §2.1, eq. (9), p.16): for every secret `s ∈ G`,
`E_k(s) = ½ Σ_{w ∈ W^k} | Σ_{t ∈ G, t ≠ 0} e_N(st) Π_{j=1}^k Ŝ_{w_j}(t) |`.

**Formalization Note** Stated for every `k ⩾ 1`; `e_N(st)` is `ZMod.stdAddChar (s * t)` and
`Ŝ_w` is the normalized transform of the indicator of the slice `S_w`. -/
theorem eq_9 (N : ℕ) [NeZero N] (k : ℕ) (hk : 1 ≤ k) (s : ZMod N) :
    insecurity N k s = (1 / 2) * ∑ w ∈ Fintype.piFinset (fun _ : Fin k => weights N),
      ‖∑ t ∈ Finset.univ.filter (fun t : ZMod N => t ≠ 0),
        ZMod.stdAddChar (s * t) * ∏ j, fhat N (slice N (w j)) t‖ := by sorry

end HWMaskLeak
