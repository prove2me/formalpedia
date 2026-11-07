-- Prove2me | Theorems.Thm_FourierEntropyApprox_fact_2_1
-- name    : FourierEntropyApprox.fact_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:45:27.693511+00:00
-- url     : https://prove2.me/theorems/0edd64ce-15c2-4871-a82b-db080b73a87f
-- title:
--   Fact 2.1 (Plancherel's Theorem): $\langle f,g\rangle=\sum_S\overline{\widehat f(S)}\,\widehat g(S)$
-- statement:
--   For any $f,g:\{-1,1\}^n\to\mathbb C$,
--
--   $$\langle f,g\rangle=\mathbb E_x\big[\overline{f(x)}\,g(x)\big]=\sum_{S\subseteq[n]}\overline{\widehat f(S)}\,\widehat g(S)=\langle\widehat f,\widehat g\rangle .$$
--
--   Plancherel's theorem expresses the orthonormality of the characters. Taking $g=f$ gives Parseval's identity $\|f\|_2^2=\sum_S|\widehat f(S)|^2$, which makes $\{|\widehat f(S)|^2\}_S$ a probability distribution for Boolean $f$, and converts the 2-norm approximation hypotheses of Theorem 3.1 into bounds on Fourier coefficients.
--
--   **Formalization Note** The left side is `cubeInner f g`, defined as $\mathbb E_x[\overline{f(x)}g(x)]$, so the page's first equality is the definition; $\langle\widehat f,\widehat g\rangle$ is written out as the sum.
--
--   Differences from the source:
--   - encoding: $\{-1,1\}^n$, $S\subseteq[n]$ → `Fin n → Bool` with true ↦ −1, `Finset (Fin n)`; reason: same points and sets
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), Fact 2.1, p.9 (PDF p.9)

import Mathlib
import Definitions.Def_FourierEntropyApprox_fourierCoeff

namespace FourierEntropyApprox

/-- **Fact 2.1 (Plancherel's Theorem).** M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), p.9:
"For any f, g : {−1, 1}ⁿ → ℂ, ⟨f, g⟩ = 𝔼ₓ[f(x)‾ g(x)] = ∑_{S⊆[n]} f̂(S)‾ ĝ(S) = ⟨f̂, ĝ⟩."

**Formalization Note.** `cubeInner f g` is `𝔼ₓ[f(x)‾ g(x)]` (its first equality is the definition), and
`⟨f̂, ĝ⟩` is written out as the sum over `S`. Conjugation is `star`. -/
theorem fact_2_1 {n : ℕ} (f g : Cube n → ℂ) :
    cubeInner f g = ∑ S : Finset (Fin n), star (fourierCoeff f S) * fourierCoeff g S := by sorry

end FourierEntropyApprox
