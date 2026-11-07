-- Prove2me | Theorems.Thm_NonadaptiveSFT_claim_11
-- name    : NonadaptiveSFT.claim_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:21:58.907507+00:00
-- url     : https://prove2.me/theorems/45dfbc38-3405-4d48-8fe0-1d6e9ca8b40d
-- title:
--   Claim 11 — $\sum_{w\in W_{\kappa'}}\frac{\kappa'}w\min\{1,(wu/\kappa')^2\}\le4u$
-- statement:
--   Let $\kappa'=2^e$ be a power of two and $W_{\kappa'}=\{1,2,4,\dots,\kappa'\}$. For every $u\ge0$,
--
--   $$\sum_{w\in W_{\kappa'}}\frac{\kappa'}w\min\Big\{1,\Big(\frac{wu}{\kappa'}\Big)^2\Big\}\le4u.\tag{15}$$
--
--   It lets the estimation errors of the multiscale test be summed over all resolutions at the cost of a constant factor.
--
--   Differences from the source:
--   - encoding: κ′ = 2^{⌈log κ⌉} for the κ ≥ 1 of Lemma 10 → κ′ = 2^e for every e ∈ ℕ; reason: every such κ′ is a power of two and every power of two arises (κ = 2^e)
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Claim 11 and eq. (15), p.24 (PDF p.26)

import Mathlib

namespace NonadaptiveSFT

/-- **Claim 11**, (15), p.24 (PDF p.26).

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…).

For every `u ≥ 0`, `Σ_{w∈W_{κ′}} (κ′/w) min{1, (wu/κ′)²} ≤ 4u`.

**Formalization Note.** `κ′ = 2^{⌈log κ⌉}` is a power of two `2^e` (`e = ⌈log₂ κ⌉ ∈ ℕ` for `κ ≥ 1`), and
`W_{κ′} = {1, 2, 4, …, κ′} = {2^i : 0 ≤ i ≤ e}` (p.17). The claim is stated for every `e ∈ ℕ`. -/
theorem claim_11 (e : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    ∑ i ∈ Finset.range (e + 1),
      ((2 : ℝ) ^ e / 2 ^ i) * min 1 ((2 ^ i * u / 2 ^ e) ^ 2) ≤ 4 * u := by sorry

end NonadaptiveSFT
