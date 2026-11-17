-- Prove2me | Theorems.Thm_FourierEntropyApprox_Supplement_theorem_4_1
-- name    : FourierEntropyApprox.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:06:25.989916+00:00
-- url     : https://prove2.me/theorems/cd8e2336-4716-4a57-9732-61678f7542bb
-- title:
--   Theorem 4.1 — moment inequality (19) for orthogonal decompositions
-- statement:
--   Let $f:\{-1,1\}^n\to\mathbb C$ and $f=\sum_{i=1}^m g_i$, where the functions $g_i:\{-1,1\}^n\to\mathbb C$ are nonzero and pairwise orthogonal: $\langle g_i,g_j\rangle=0$ for $i\ne j$. Put $p_i=\|g_i\|_2^2$ and $L_i=\|\widehat{g_i}\|_1$. Then for every real $r$ with $1\le r\le2$,
--
--   $$\sum_{S\subseteq[n]}|\widehat f(S)|^r\le\sum_{i=1}^m L_i^{2-r}\,p_i^{r-1},$$
--
--   and equality holds at $r=2$.
--
--   The inequality interpolates between the triangle inequality ($r=1$) and Parseval ($r=2$). Theorem 4.2 differentiates it at $r=2$ to obtain an entropy bound.
--
--   **Formalization Note** The family is indexed by `Fin m`; orthogonality uses the base inner product `cubeInner`; powers are real powers. The equality clause is the displayed inequality at $r=2$ written with $=$.
--
--   Differences from the source:
--   - encoding: $f,g_i:\{-1,1\}^n\to\mathbb C$, $S\subseteq[n]$, $i\in[m]$ → functions on Fin n → Bool (true = −1) with values in ℂ, Finset (Fin n), Fin m; reason: the base mission's published conventions; same functions and index sets
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), Theorem 4.1 and (19), p.16 (PDF p.16)

import Mathlib
import Definitions.Def_FourierEntropyApprox_fourierCoeff

set_option autoImplicit false

namespace FourierEntropyApprox

namespace Supplement

/-- **Theorem 4.1.** M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), p.16:
"Let f : {−1, 1}ⁿ → ℂ and f = ∑_{i=1}^m gᵢ where the non-zero functions gᵢ : {−1, 1}ⁿ → ℂ are pairwise
orthogonal. Define pᵢ := ‖gᵢ‖₂² and Lᵢ := ‖ĝᵢ‖₁. Then, for every 1 ≤ r ≤ 2,
∑_{S⊆[n]} |f̂(S)|^r ≤ ∑_{i=1}^m Lᵢ^{2−r} pᵢ^{r−1}. (19) Equality holds at r = 2."

**Formalization Note.** The family `g` is indexed by `Fin m` (`m = 0` allowed); "non-zero" is `g i ≠ 0` as
a function; pairwise orthogonal is `⟨gᵢ, gⱼ⟩ = 0` for `i ≠ j` with the base inner product `cubeInner`
(p.8). `pᵢ` is `l2NormSq (g i)` and `Lᵢ` is `spectralNorm (g i)`. Powers are real powers (`Real.rpow`);
`|f̂(S)|^r = 0` when `f̂(S) = 0` since `r ≥ 1`. The second conjunct is (19) at `r = 2` with equality. -/
theorem theorem_4_1 (n m : ℕ) (f : Cube n → ℂ) (g : Fin m → Cube n → ℂ)
    (hf : f = ∑ i, g i) (hg : ∀ i, g i ≠ 0)
    (horth : ∀ i j, i ≠ j → cubeInner (g i) (g j) = 0) :
    (∀ r : ℝ, 1 ≤ r → r ≤ 2 →
      ∑ S : Finset (Fin n), ‖fourierCoeff f S‖ ^ r ≤
        ∑ i, spectralNorm (g i) ^ (2 - r) * l2NormSq (g i) ^ (r - 1)) ∧
    ∑ S : Finset (Fin n), ‖fourierCoeff f S‖ ^ (2 : ℝ) =
      ∑ i, spectralNorm (g i) ^ ((2 : ℝ) - 2) * l2NormSq (g i) ^ ((2 : ℝ) - 1) := by sorry

end Supplement

end FourierEntropyApprox
