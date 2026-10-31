-- Prove2me | Theorems.Thm_KempeCloning_binomial_normalization
-- name    : KempeCloning.binomial_normalization
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:07.163273+00:00
-- url     : https://prove2.me/theorems/0cd67a50-d67e-456f-9800-e53cde99b674
-- title:
--   Sentence after (19): $\sum_{i=0}^{l}\binom{m+i}{m} = \binom{m+l+1}{l}$
-- statement:
--   For all natural numbers $m$ and $l$,
--
--   $$\sum_{i=0}^{l}\binom{m+i}{m} = \binom{m+l+1}{l}.$$
--
--   This is the identity the paper quotes to show that the cloner states $|\mathcal F_l\rangle$ of (19) are normalized: the squared amplitudes of $|\mathcal F_l\rangle$ are $\binom{m+l-i}{m}/\binom{m+l+1}{l}$, $i = 0,\dots,l$.
--
--   Differences from the source:
--   - reading: the identity for the $m, l$ of (19), "for arbitrary $N$ and $m$" (p.5) → every $m, l\in\mathbb N$, including $m = 0$; reason: the page does not exclude $m = 0$; the stronger reading is taken
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II C, sentence after (19), p.5

import Mathlib

namespace KempeCloning

/-- **The binomial identity behind the normalization of `|F_l⟩`.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II C, sentence after (19), p.5: "To see that
|F_l⟩ is properly normalized note that Σ_{i=0}^{l} binom(m+i, m) = binom(m+l+1, l)."

For all natural numbers `m, l`: `Σ_{i=0}^{l} binom(m + i, m) = binom(m + l + 1, l)`. -/
theorem binomial_normalization (m l : ℕ) :
    ∑ i ∈ Finset.range (l + 1), (m + i).choose m = (m + l + 1).choose l := by sorry

end KempeCloning
