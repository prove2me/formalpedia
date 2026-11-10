-- Prove2me | Theorems.Thm_NoStretch1PRS_lemma_3_6
-- name    : NoStretch1PRS.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:05:29.500821+00:00
-- url     : https://prove2.me/theorems/80ba57ae-ff04-4073-b145-a7e09b1db1aa
-- title:
--   Lemma 3.6 — energy estimation by evolution for time $\pi$
-- statement:
--   Let $\mathcal H$ be a Hilbert space of dimension $d$, $H$ a Hermitian matrix on $\mathcal H$ with $0\preceq H\preceq I$, $|\phi\rangle$ a state and $p=\langle\phi|H|\phi\rangle$. Then
--
--   $$p^2\le\frac{1-\mathrm{Re}\,\langle\phi|e^{\mathrm i\pi H}|\phi\rangle}{2}\le\frac{\pi^2}{4}\,p .$$
--
--   The middle quantity is the probability that a Hadamard test with a controlled $e^{\mathrm i\pi H}=O_{2,\alpha}$ outputs $1$; Theorem 4.7's adversary is that Hadamard test.
--
--   Differences from the source:
--
--   - encoding: p = ⟨ϕ|H|ϕ⟩ → p = Re⟨ϕ|H|ϕ⟩; reason: ⟨ϕ|H|ϕ⟩ is real for Hermitian H
-- source:
--   Chen, Coladangelo, Lin, Skoumios, Tysdal, Wang, No linear stretching of single-copy quantum pseudorandomness, arXiv:2606.24736 (held version, sha256 2670cb2f…), Lemma 3.6, p.18

import Mathlib

set_option autoImplicit false

namespace NoStretch1PRS

open Matrix
open scoped ComplexOrder

/-- **Lemma 3.6 (energy estimation by evolution for time `π`).**
B. Chen, A. Coladangelo, Y.-T. Lin, N. Skoumios, J. Tysdal, Y. Wang, *No linear stretching of
single-copy quantum pseudorandomness*, arXiv:2606.24736 (held version, sha256 2670cb2f…), Lemma 3.6, p.18.

Let `H` be a Hermitian matrix on a `d`-dimensional Hilbert space with `0 ⪯ H ⪯ I`, `|ϕ⟩` a unit
vector and `p = ⟨ϕ|H|ϕ⟩`. Then `p² ≤ (1 − Re⟨ϕ|e^{iπH}|ϕ⟩)/2 ≤ (π²/4) p`.

**Formalization Note.** `p` is real for Hermitian `H`; it is taken as the real part. -/
theorem lemma_3_6 (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ) (h0 : H.PosSemidef)
    (h1 : (1 - H).PosSemidef) (ϕ : Fin d → ℂ) (hϕ : star ϕ ⬝ᵥ ϕ = 1) :
    (star ϕ ⬝ᵥ (H *ᵥ ϕ)).re ^ 2 ≤
        (1 - (star ϕ ⬝ᵥ (NormedSpace.exp (((Real.pi : ℂ) * Complex.I) • H) *ᵥ ϕ)).re) / 2 ∧
      (1 - (star ϕ ⬝ᵥ (NormedSpace.exp (((Real.pi : ℂ) * Complex.I) • H) *ᵥ ϕ)).re) / 2 ≤
        Real.pi ^ 2 / 4 * (star ϕ ⬝ᵥ (H *ᵥ ϕ)).re := by sorry

end NoStretch1PRS
