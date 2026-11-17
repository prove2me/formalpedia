-- Prove2me | Theorems.Thm_FourierEntropyApprox_Supplement_theorem_4_2
-- name    : FourierEntropyApprox.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:06:48.57913+00:00
-- url     : https://prove2.me/theorems/819b4890-a662-4e16-b58f-d89a86d0a5ce
-- title:
--   Theorem 4.2 — entropy bound (22) for orthogonal decompositions
-- statement:
--   Let $f:\{-1,1\}^n\to\mathbb C$ and $f=\sum_{i=1}^m g_i$, where the functions $g_i$ are nonzero and pairwise orthogonal. Put $p_i=\|g_i\|_2^2$ and $L_i=\|\widehat{g_i}\|_1$. Then
--
--   $$\mathcal E(\widehat f^2)=\sum_{S\subseteq[n]}|\widehat f(S)|^2\log_2\frac{1}{|\widehat f(S)|^2}\le 2\sum_{i=1}^m p_i\log_2\frac{L_i}{p_i}.$$
--
--   Here $f$ need not be Boolean or normalized. Applied to the indicator functions of the cells of an unambiguous certificate, the bound gives Theorem 4.3.
--
--   **Formalization Note** $\mathcal E(\widehat f^2)$ is the base `entropyFun f` (with $0\log(1/0)=0$); $p_i$ is `l2NormSq (g i)`, $L_i$ is `spectralNorm (g i)`; logarithms are base two.
--
--   Differences from the source:
--   - encoding: $f,g_i:\{-1,1\}^n\to\mathbb C$, $S\subseteq[n]$, $i\in[m]$ → functions on Fin n → Bool (true = −1) with values in ℂ, Finset (Fin n), Fin m; reason: the base mission's published conventions; same functions and index sets
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), Theorem 4.2 and (22), p.17 (PDF p.17)

import Mathlib
import Definitions.Def_FourierEntropyApprox_entropyFun

set_option autoImplicit false

namespace FourierEntropyApprox

namespace Supplement

/-- **Theorem 4.2.** M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), p.17:
"Let f : {−1, 1}ⁿ → ℂ and f = ∑_{i=1}^m gᵢ where the non-zero functions gᵢ : {−1, 1}ⁿ → ℂ are pairwise
orthogonal. Define pᵢ := ‖gᵢ‖₂² and Lᵢ := ‖ĝᵢ‖₁. Then,
ℰ(f̂²) = ∑_{S⊆[n]} |f̂(S)|² log 1/|f̂(S)|² ≤ 2 ∑_{i=1}^m pᵢ log Lᵢ/pᵢ. (22)"

**Formalization Note.** Same hypotheses and encoding as Theorem 4.1 (`Fin m`, `g i ≠ 0`, `cubeInner`
orthogonality, `pᵢ = l2NormSq (g i)`, `Lᵢ = spectralNorm (g i)`). `ℰ(f̂²)` is the base `entropyFun f`
((8), p.9, with `0 log(1/0) = 0`); `f` need not be Boolean or normalized. Logarithms are base two (p.2). -/
theorem theorem_4_2 (n m : ℕ) (f : Cube n → ℂ) (g : Fin m → Cube n → ℂ)
    (hf : f = ∑ i, g i) (hg : ∀ i, g i ≠ 0)
    (horth : ∀ i j, i ≠ j → cubeInner (g i) (g j) = 0) :
    entropyFun f ≤
      2 * ∑ i, l2NormSq (g i) * Real.logb 2 (spectralNorm (g i) / l2NormSq (g i)) := by sorry

end Supplement

end FourierEntropyApprox
