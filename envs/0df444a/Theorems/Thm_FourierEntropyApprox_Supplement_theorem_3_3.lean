-- Prove2me | Theorems.Thm_FourierEntropyApprox_Supplement_theorem_3_3
-- name    : FourierEntropyApprox.Supplement.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:06:02.158442+00:00
-- url     : https://prove2.me/theorems/b2ecd217-e573-4bd6-8f4b-74332dca0a7b
-- title:
--   Theorem 3.3 — $\mathbb H(\widehat f^2)=O(R^{\oplus}(f))$
-- statement:
--   Let $f:\{-1,1\}^n\to\{-1,1\}$ be a Boolean function, $\mathbb H(\widehat f^2)$ its Fourier entropy, and $R^{\oplus}(f)$ its randomized parity-decision-tree complexity with error at most $1/3$ on every input. There is an absolute constant $K>0$ such that for every $n$ and every Boolean $f$,
--
--   $$\mathbb H(\widehat f^2)\le K\,R^{\oplus}(f).$$
--
--   In particular the Fourier entropy is bounded by a constant multiple of the ordinary randomized query complexity $R(f)$. The bound extends earlier results for min-entropy and Rényi entropies of order greater than one to Shannon entropy.
--
--   **Formalization Note** $\mathbb H(\widehat f^2)$ is the base `entropyFun f` and $R^{\oplus}(f)$ is `Rparity f`. Constant functions, with $R^{\oplus}(f)=0$, are included.
--
--   Differences from the source:
--   - encoding: $O(\cdot)$ with an unspecified constant → one constant $K>0$ chosen before $n$ and $f$; reason: the meaning of $O(\cdot)$ for a statement over all $n$ and all Boolean $f$, as in the published goal
--   - encoding: $f:\{-1,1\}^n\to\{-1,1\}$ → real-valued $f$ on Fin n → Bool with IsBoolean f (true = −1); reason: the base mission's published conventions; same functions
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), Theorem 3.3, p.16 (PDF p.16); R⊕ defined pp.12–13

import Mathlib
import Definitions.Def_FourierEntropyApprox_entropyFun
import Definitions.Def_FourierEntropyApprox_IsBoolean
import Definitions.Def_FourierEntropyApprox_Supplement_RPDT

set_option autoImplicit false

namespace FourierEntropyApprox

namespace Supplement

/-- **Theorem 3.3.** M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), p.16:
"Let f : {−1, 1}ⁿ → {−1, 1} be a Boolean function and R⊕(f) be the randomized parity-decision tree complexity
of f with error at most 1/3. Then, ℍ(f̂²) = O(R⊕(f))."

There is an absolute constant `K > 0` such that for every `n` and every Boolean `f : {−1, 1}ⁿ → {−1, 1}`,
`ℍ(f̂²) ≤ K · R⊕(f)`.

**Formalization Note.** `ℍ(f̂²)` is the base `entropyFun f` (Definition 2.2, p.9). `R⊕(f)` is `Rparity f`
(p.13): worst-case depth over the trees of positive probability, error at most `1/3` on every input, parity
queries `χ_S` for arbitrary `S ⊆ [n]`. The `O(·)` is one constant `K`, chosen before `n` and `f`.
`R⊕(f) = 0` (constant `f`) is not excluded. -/
theorem theorem_3_3 :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (f : Cube n → ℝ), IsBoolean f →
      entropyFun f ≤ K * (Rparity f : ℝ) := by sorry

end Supplement

end FourierEntropyApprox
