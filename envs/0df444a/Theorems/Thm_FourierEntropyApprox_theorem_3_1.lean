-- Prove2me | Theorems.Thm_FourierEntropyApprox_theorem_3_1
-- name    : FourierEntropyApprox.theorem_3_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T21:46:21.95135+00:00
-- url     : https://prove2.me/theorems/5a8bf180-1648-4353-87b0-d89d7bd8c3b3
-- title:
--   Theorem 3.1, bound (13): approximants at every accuracy $2^{-j}$ bound the entropy, $\mathcal E(\widehat f^2)\le6+4CK_aL$
-- statement:
--   Let $f:\{-1,1\}^n\to\mathbb C$ with $\|f\|_2^2\le1$. Suppose that $a\ge0$, $C>0$, $L\ge1$, and that for every integer $j\ge1$ there is a function $P_j:\{-1,1\}^n\to\mathbb C$ with
--
--   $$\|f-P_j\|_2^2\le2^{-j}\qquad\text{and}\qquad\log_2\max\{1,\|\widehat{P_j}\|_1\}\le CL(j+1)^a. \tag{12}$$
--
--   Then
--
--   $$\mathcal E(\widehat f^2)\le6+4CK_aL=O_{a,C}(L),\qquad K_a=\sum_{j\ge1}2^{-j}(j+3)^a. \tag{13}$$
--
--   This is the paper's approximation theorem: a function that can be approximated at every accuracy $2^{-j}$ by functions whose log-spectral norm grows polynomially in $j$ has Fourier entropy linear in the growth parameter $L$. Theorem 3.2 is its application to majority-amplified approximating polynomials.
--
--   **Formalization Note** The approximants are a family indexed by $\mathbb N$; its value at $j=0$ is unconstrained and unused. $(j+1)^a$ is a real power. $K_a$ is `Ka a`; its convergence and the bound $K_a=O(2^a a!)$ are the companion milestone `theorem_3_1_Ka`.
--
--   Differences from the source:
--   - encoding: for every integer $j\ge1$ there is $P_j$ → a family $P:\mathbb N\to(\{-1,1\}^n\to\mathbb C)$ satisfying (12) for every $j\ge1$; reason: the two forms are equivalent by choice; $P_0$ is unused
--   - reading: $=O_{a,C}(L)$ in (13) → not a separate clause; reason: it follows from the explicit bound, since $6+4CK_aL\le(6+4CK_a)L$ for $L\ge1$
--   - encoding: $\{-1,1\}^n$, $S\subseteq[n]$ → `Fin n → Bool` with true ↦ −1, `Finset (Fin n)`; reason: same points and sets
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), Theorem 3.1, eqs. (12)–(13), p.14 (PDF p.14)

import Mathlib
import Definitions.Def_FourierEntropyApprox_entropyFun
import Definitions.Def_FourierEntropyApprox_Ka

namespace FourierEntropyApprox

/-- **Theorem 3.1, bound (13).** M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), p.14:
"Let f : {−1, 1}ⁿ → ℂ with ‖f‖₂² ≤ 1. Suppose that a ≥ 0, C > 0, L ≥ 1, and for any integer j ≥ 1, there is a
function P_j : {−1, 1}ⁿ → ℂ such that ‖f − P_j‖₂² ≤ 2^{−j} and log max{1, ‖P̂_j‖₁} ≤ CL(j + 1)^a. (12)
Then, ℰ(f̂²) ≤ 6 + 4CK_aL = O_{a,C}(L), (13) where K_a = ∑_{j≥1} 2^{−j}(j + 3)^a = O(2^a a!)."

**Formalization Note.** The approximants are a family `P : ℕ → Cube n → ℂ`; the value at `j = 0` is
unconstrained and unused. Logarithms are base two (p.2); `(j + 1)^a` is a real power. `K_a` is `Ka a`, whose
summability and the bound `O(2^a a!)` are `theorem_3_1_Ka`. The `O_{a,C}(L)` in (13) follows from the explicit
bound, as `6 + 4CK_aL ≤ (6 + 4CK_a)L` for `L ≥ 1`. -/
theorem theorem_3_1 {n : ℕ} (f : Cube n → ℂ) (a C L : ℝ) (P : ℕ → Cube n → ℂ)
    (hf : l2NormSq f ≤ 1) (ha : 0 ≤ a) (hC : 0 < C) (hL : 1 ≤ L)
    (hP : ∀ j : ℕ, 1 ≤ j → l2NormSq (f - P j) ≤ ((2 : ℝ) ^ j)⁻¹ ∧
      Real.logb 2 (max 1 (spectralNorm (P j))) ≤ C * L * ((j : ℝ) + 1) ^ a) :
    entropyFun f ≤ 6 + 4 * C * Ka a * L := by sorry

end FourierEntropyApprox
