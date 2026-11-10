-- Prove2me | Theorems.Thm_NoStretch1PRS_lemma_3_4
-- name    : NoStretch1PRS.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:05:32.696394+00:00
-- url     : https://prove2.me/theorems/b098f1fd-11d9-453b-a38a-d1a229e22d1f
-- title:
--   Lemma 3.4 — trace against a spread-out state
-- statement:
--   Let $M,\sigma$ be positive semidefinite Hermitian matrices with $\mathrm{Tr}(\sigma)=1$ and $0\preceq\sigma\preceq I/d$ for some $d\ge1$. Then for every real $s\ge1$,
--
--   $$\mathrm{Tr}(M\sigma)\le\Big(\frac{\mathrm{Tr}\,M^s}{d}\Big)^{1/s}.$$
--
--   Proposition 4.6 applies it with the non-integer exponent $s=\varepsilon_4$ to bound the acceptance of a Haar-random input through the spectrum of the test.
--
--   Differences from the source:
--
--   - encoding: M^s and the traces Tr(Mσ), Tr M^s → spectral power of the Hermitian M (x ↦ x^s on eigenvalues); real parts of the traces; reason: both traces are real for positive semidefinite M, σ
-- source:
--   Chen, Coladangelo, Lin, Skoumios, Tysdal, Wang, No linear stretching of single-copy quantum pseudorandomness, arXiv:2606.24736 (held version, sha256 2670cb2f…), Lemma 3.4, p.17

import Mathlib

set_option autoImplicit false

namespace NoStretch1PRS

open Matrix
open scoped ComplexOrder

/-- **Lemma 3.4 (trace against a spread-out state).**
B. Chen, A. Coladangelo, Y.-T. Lin, N. Skoumios, J. Tysdal, Y. Wang, *No linear stretching of
single-copy quantum pseudorandomness*, arXiv:2606.24736 (held version, sha256 2670cb2f…), Lemma 3.4, p.17.

Let `M, σ` be positive semidefinite matrices with `Tr σ = 1` and `0 ⪯ σ ⪯ I/d` for some real
`d ≥ 1`. Then for every real `s ≥ 1`, `Tr(Mσ) ≤ (Tr M^s / d)^{1/s}`.

**Formalization Note.** `M^s` is the spectral power (`IsHermitian.cfc` of `x ↦ x^s`), defined for
real `s`. The traces `Tr(Mσ)` (of a product of positive semidefinite matrices) and `Tr M^s`
are real and are taken as real parts. -/
theorem lemma_3_4 {ι : Type} [Fintype ι] [DecidableEq ι] (M σ : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (hσ : σ.PosSemidef) (d : ℝ) (hd : 1 ≤ d) (htr : σ.trace = 1)
    (hle : (((d : ℂ))⁻¹ • (1 : Matrix ι ι ℂ) - σ).PosSemidef) (s : ℝ) (hs : 1 ≤ s) :
    (M * σ).trace.re ≤ ((hM.1.cfc fun x => x ^ s).trace.re / d) ^ (1 / s) := by sorry

end NoStretch1PRS
