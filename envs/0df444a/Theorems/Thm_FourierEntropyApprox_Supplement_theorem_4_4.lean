-- Prove2me | Theorems.Thm_FourierEntropyApprox_Supplement_theorem_4_4
-- name    : FourierEntropyApprox.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:08:12.341577+00:00
-- url     : https://prove2.me/theorems/05306bcc-743c-4978-9bc1-590ce00a8459
-- title:
--   Theorem 4.4 — moment and entropy bounds (27), (28) under a diagonal Gram majorant
-- statement:
--   Let $f:\{-1,1\}^n\to\mathbb C$ and $f=\sum_{i=1}^m g_i$ with nonzero functions $g_i:\{-1,1\}^n\to\mathbb C$. Let $\Gamma$ be the $m\times m$ Gram matrix $\Gamma_{ij}=\langle g_i,g_j\rangle$, and $L_i=\|\widehat{g_i}\|_1$. Suppose there are numbers $a_i>0$ with
--
--   $$\Gamma\preceq D:=\operatorname{diag}(a_1,\dots,a_m)$$
--
--   in the Loewner order. Then:
--
--   1. for every real $r$ with $1\le r\le2$,
--   $$\sum_{S\subseteq[n]}|\widehat f(S)|^r\le\sum_{i=1}^m L_i^{2-r}a_i^{r-1};$$
--   2. if in addition $\sum_i a_i=\|f\|_2^2$ (equality at $r=2$), then
--   $$\mathcal E(\widehat f^2)\le 2\sum_{i=1}^m a_i\log_2\frac{L_i}{a_i}.$$
--
--   This generalizes Theorems 4.1 and 4.2 to decompositions whose terms are not orthogonal, such as conical juntas with overlapping terms (Theorem 4.5).
--
--   **Formalization Note** $\langle g_i,g_j\rangle$ is the base `cubeInner`, $\mathbb E_x[\overline{g_i(x)}g_j(x)]$; $\Gamma\preceq D$ is positive semidefiniteness of $D-\Gamma$ over $\mathbb C$; $\|f\|_2^2$ is `l2NormSq f`.
--
--   Differences from the source:
--   - encoding: $\Gamma\preceq D$ → (D − Γ).PosSemidef over ℂ; reason: the Loewner order; same matrices
--   - encoding: $f,g_i:\{-1,1\}^n\to\mathbb C$, $S\subseteq[n]$, $i\in[m]$ → functions on Fin n → Bool (true = −1) with values in ℂ, Finset (Fin n), Fin m; reason: the base mission's published conventions; same functions and index sets
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), Theorem 4.4, (26)–(28), pp.18–19 (PDF pp.18–19)

import Mathlib
import Definitions.Def_FourierEntropyApprox_entropyFun

open scoped ComplexOrder

set_option autoImplicit false

namespace FourierEntropyApprox

namespace Supplement

/-- **Theorem 4.4.** M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), pp.18–19:
"Let f : {−1, 1}ⁿ → ℂ and f = ∑_{i=1}^m gᵢ where gᵢ : {−1, 1}ⁿ → ℂ's are non-zero functions. Define m × m Gram
matrix Γ where Γᵢⱼ := ⟨gᵢ, gⱼ⟩ = 𝔼[g̅ᵢgⱼ], and denote Lᵢ := ‖ĝᵢ‖₁. Suppose there are numbers aᵢ > 0 such that
Γ ⪯ D := diag(a₁, …, a_m). (26) Then, for every 1 ≤ r ≤ 2, ∑_{S⊆[n]} |f̂(S)|^r ≤ ∑_{i=1}^m Lᵢ^{2−r} aᵢ^{r−1}. (27)
If, additionally, the equality holds at r = 2, ∑ᵢ aᵢ = ‖f‖₂², then ℰ(f̂²) ≤ 2 ∑_{i=1}^m aᵢ log Lᵢ/aᵢ. (28)"

**Formalization Note.** `Γᵢⱼ = cubeInner (g i) (g j) = 𝔼ₓ[conj(gᵢ(x)) gⱼ(x)]`, the inner product of p.8. `Γ ⪯ D` is the Loewner order: `D − Γ` is
positive semidefinite over `ℂ`. The family is indexed by `Fin m`; `Lᵢ = spectralNorm (g i)`; powers are
`Real.rpow`; `ℰ(f̂²)` is `entropyFun f`, `‖f‖₂²` is `l2NormSq f`, logarithms are base two. Conclusion
(27) holds for every `r ∈ [1, 2]` unconditionally; (28) under the extra hypothesis `∑ aᵢ = ‖f‖₂²`. -/
theorem theorem_4_4 (n m : ℕ) (f : Cube n → ℂ) (g : Fin m → Cube n → ℂ)
    (hf : f = ∑ i, g i) (hg : ∀ i, g i ≠ 0) (a : Fin m → ℝ) (ha : ∀ i, 0 < a i)
    (hΓ : (Matrix.diagonal (fun i => (a i : ℂ)) -
      Matrix.of (fun i j => cubeInner (g i) (g j))).PosSemidef) :
    (∀ r : ℝ, 1 ≤ r → r ≤ 2 →
      ∑ S : Finset (Fin n), ‖fourierCoeff f S‖ ^ r ≤
        ∑ i, spectralNorm (g i) ^ (2 - r) * a i ^ (r - 1)) ∧
    (∑ i, a i = l2NormSq f →
      entropyFun f ≤ 2 * ∑ i, a i * Real.logb 2 (spectralNorm (g i) / a i)) := by sorry

end Supplement

end FourierEntropyApprox
