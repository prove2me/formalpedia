-- Prove2me | Theorems.Thm_HWMaskLeak_eq_40
-- name    : HWMaskLeak.eq_40
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:32.705666+00:00
-- url     : https://prove2.me/theorems/bcfc9026-e8de-4eb3-8b7e-e4400bd088fa
-- title:
--   Eq. (40) — $\Delta_m$ is the average of $E_m(s)$
-- statement:
--   For every $N\ge1$ and every $m\ge1$,
--   $$
--   \Delta_m=\frac1N\sum_{s\in G}\frac12\sum_{w\in W^m}\Bigl|\sum_{t\ne0}e_N(st)\prod_{j=1}^m\hat S_{w_j}(t)\Bigr|=\frac1N\sum_{s\in G}E_m(s).
--   $$
--
--   The first equality is the Fourier inversion (38) of the probabilistic definition (3) of $\Delta_m$, the second is (9) averaged over the secret. It turns bounds on $E_m(s)$ that are uniform in $s$ into bounds on $\Delta_m$.
--
--   Differences from the source:
--   - encoding: laws of uniform random shares, total variation distance → normalized counts on finite sets and ½ Σ |P − Q| over W^k (resp. W^m × G); reason: uniform choices on finite sets are counting measures; the summation range contains both supports, so no instance changes
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), App. D.2, p.53, eq. (40), with (38), p.52

import Mathlib
import Definitions.Def_HWMaskLeak_insecurity
import Definitions.Def_HWMaskLeak_maskSumDist
import Definitions.Def_HWMaskLeak_fhat
import Definitions.Def_HWMaskLeak_slice

namespace HWMaskLeak

/-- **Eq. (40), `Δ_m` is the average of `E_m`** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), App. D.2, eq. (40), p.53, with (38), p.52): for
every `m ⩾ 1`,
`Δ_m = (1/N) Σ_{s ∈ G} ½ Σ_{w ∈ W^m} | Σ_{t ≠ 0} e_N(st) Π_{j=1}^m Ŝ_{w_j}(t) | = (1/N) Σ_{s ∈ G} E_m(s)`.

**Formalization Note** `Δ_m` is the probabilistic distance (3), so the first equality is (38). -/
theorem eq_40 (N : ℕ) [NeZero N] (m : ℕ) (hm : 1 ≤ m) :
    maskSumDist N m = (1 / (N : ℝ)) * ∑ s : ZMod N,
        (1 / 2) * ∑ w ∈ Fintype.piFinset (fun _ : Fin m => weights N),
          ‖∑ t ∈ Finset.univ.filter (fun t : ZMod N => t ≠ 0),
            ZMod.stdAddChar (s * t) * ∏ j, fhat N (slice N (w j)) t‖ ∧
    (1 / (N : ℝ)) * ∑ s : ZMod N,
        (1 / 2) * ∑ w ∈ Fintype.piFinset (fun _ : Fin m => weights N),
          ‖∑ t ∈ Finset.univ.filter (fun t : ZMod N => t ≠ 0),
            ZMod.stdAddChar (s * t) * ∏ j, fhat N (slice N (w j)) t‖ =
      (1 / (N : ℝ)) * ∑ s : ZMod N, insecurity N m s := by sorry

end HWMaskLeak
