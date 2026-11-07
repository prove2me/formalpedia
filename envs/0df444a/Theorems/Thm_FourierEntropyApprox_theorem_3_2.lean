-- Prove2me | Theorems.Thm_FourierEntropyApprox_theorem_3_2
-- name    : FourierEntropyApprox.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:46:38.495514+00:00
-- url     : https://prove2.me/theorems/31fdbaf2-452a-4570-875f-1da16104d63b
-- title:
--   Theorem 3.2: $\mathbb H(\widehat f^2)=O(\log(1+\|\widehat f\|_{1,\varepsilon}))$ for every fixed $0\le\varepsilon<1$
-- statement:
--   For every $\varepsilon$ with $0\le\varepsilon<1$ there is a constant $K>0$, depending only on $\varepsilon$, such that for every $n$ and every Boolean function $f:\{-1,1\}^n\to\{-1,1\}$,
--
--   $$\mathbb H(\widehat f^2)\le K\log_2\big(1+\|\widehat f\|_{1,\varepsilon}\big).$$
--
--   Here $\mathbb H(\widehat f^2)=\sum_S|\widehat f(S)|^2\log_2\frac{1}{|\widehat f(S)|^2}$ is the Fourier entropy of $f$ and $\|\widehat f\|_{1,\varepsilon}$ is the least spectral norm of a real polynomial $p$ with $|p(x)-f(x)|\le\varepsilon$ at every $x$.
--
--   The elementary bound $\mathbb H(\widehat f^2)\le2\log\|\widehat f\|_1$ needs the spectral norm of $f$ itself; the theorem shows that a pointwise approximation at any fixed error below one suffices. Before it, only the min-entropy and Rényi entropies of order greater than one were known to be bounded by the approximate spectral norm (Arunachalam, Chakraborty, Koucký, Saurabh and de Wolf). The paper derives from it the bound $\mathbb H(\widehat f^2)=O(R_\oplus(f))$ by randomized parity-decision-tree complexity.
--
--   **Formalization Note** The page writes $\mathbb H(f)$ for $\mathbb H(\widehat f^2)$. $K$ is chosen after $\varepsilon$ and before $n$ and $f$. No additive constant is needed: every $\varepsilon$-approximant $p$ has $\|\widehat p\|_1\ge|p(x)|\ge1-\varepsilon$, so the right side is at least $K\log_2(2-\varepsilon)>0$. At $\varepsilon=1$ the statement is false (the zero polynomial approximates every Boolean function).
--
--   Differences from the source:
--   - generalization: "for $\varepsilon>0$", with the proof's "without loss of generality $\varepsilon=1/3$" → every $\varepsilon$ with $0\le\varepsilon<1$, including $\varepsilon=0$; reason: p.3 states the result "for any other fixed $0\le\varepsilon<1$"; the case $\varepsilon=0$ follows from $\varepsilon=1/3$ because $\|\widehat f\|_{1,1/3}\le\|\widehat f\|_{1,0}$
--   - reading: "for $\varepsilon>0$" → $\varepsilon<1$; reason: $\|\widehat f\|_{1,\varepsilon}$ is defined only for $0\le\varepsilon<1$ (p.8), and the statement is false at $\varepsilon\ge1$, where $p=0$ is an approximant and the right side is $0$ while AND on two bits has entropy $2$
--   - reading: $=O(\log(1+\|\widehat f\|_{1,\varepsilon}))$ → there is $K>0$ depending only on $\varepsilon$, chosen before $n$ and $f$, with no additive constant; reason: p.3 "with a constant depending only on $\varepsilon$"; an additive constant would be absorbed, since $\log_2(1+\|\widehat f\|_{1,\varepsilon})\ge\log_2(2-\varepsilon)>0$
--   - encoding: $\mathbb H(f)$ → $\mathbb H(\widehat f^2)$, the Fourier entropy of Definition 2.2; reason: the paper's shorthand; its proof ends with $\mathbb H(\widehat f^2)$
--   - encoding: the minimum over polynomials $p$ → the infimum over real functions $p$ on the cube; reason: real functions on the cube are the real multilinear polynomials, the feasible set is nonempty and bounded below, and the minimum is attained
--   - encoding: $f:\{-1,1\}^n\to\{-1,1\}$ → a real function on `Fin n → Bool` (true ↦ −1) taking only the values $\pm1$; reason: same functions
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), Theorem 3.2, p.15 (PDF p.15); range of ε, p.3, after display (1)

import Mathlib
import Definitions.Def_FourierEntropyApprox_entropyFun
import Definitions.Def_FourierEntropyApprox_IsBoolean
import Definitions.Def_FourierEntropyApprox_approxSpectralNorm

namespace FourierEntropyApprox

/-- **Theorem 3.2.** M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), p.15:
"Let f : {−1, 1}ⁿ → {−1, 1} be a Boolean function. Then, for ε > 0, ℍ(f) = O(log(1 + ‖f̂‖_{1,ε}))."
Context, p.3: "For any other fixed 0 ≤ ε < 1, the same statement holds with a constant depending only on ε."

For every `ε` with `0 ≤ ε < 1` there is `K > 0` such that for every `n` and every Boolean
`f : {−1, 1}ⁿ → {−1, 1}`, `ℍ(f̂²) ≤ K · log₂(1 + ‖f̂‖_{1,ε})`.

**Formalization Note.** `ℍ(f)` is the paper's shorthand for the Fourier entropy `ℍ(f̂²)` (Definition 2.2,
p.9), here `entropyFun f`. `‖f̂‖_{1,ε}` is `approxSpectralNorm ε f`, defined on p.8 for `0 ≤ ε < 1`.
The constant `K` depends on `ε` only: it is chosen before `n` and `f`. No additive constant is needed, since
`‖f̂‖_{1,ε} ≥ 1 − ε > 0`. Logarithms are base two (p.2). -/
theorem theorem_3_2 :
    ∀ ε : ℝ, 0 ≤ ε → ε < 1 → ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (f : Cube n → ℝ), IsBoolean f →
      entropyFun f ≤ K * Real.logb 2 (1 + approxSpectralNorm ε f) := by sorry

end FourierEntropyApprox
