-- Prove2me | Theorems.Thm_GaussianMatrix_sMin_lipschitz
-- name    : GaussianMatrix.sMin_lipschitz
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T03:27:45.982326+00:00
-- url     : https://prove2.me/theorems/6a5bff5e-3014-4570-9a22-23a5e199c5d1
-- title:
--   The smallest singular value is $1$-Lipschitz for the Frobenius norm: $|\sigma_{\min}(A)-\sigma_{\min}(B)|\le\|A-B\|_F$
-- statement:
--   Let $A, B \in \mathbb{R}^{N\times n}$ be real matrices, and let
--   $$\sigma_{\min}(A) = \inf\{\, \|Ax\|_2 : x \in \mathbb{R}^n,\ \|x\|_2 = 1 \,\}$$
--   denote the smallest singular value of $A$ (with the convention $\inf\emptyset = 0$, so $\sigma_{\min} = 0$ when $n = 0$), and let $\|M\|_F = \big(\sum_{i,j} M_{ij}^2\big)^{1/2}$ denote the Frobenius norm. Then
--   $$\big|\sigma_{\min}(A) - \sigma_{\min}(B)\big| \;\le\; \|A - B\|_F .$$
--
--   This is the Lipschitz estimate that makes Gaussian concentration applicable to the smallest singular value of a Gaussian matrix: combined with Gordon's bound $\mathbb{E}\,\sigma_{\min}(G) \ge \sqrt N - \sqrt n$, it yields the lower tail $\mathbb{P}\{\sigma_{\min}(G) \le \sqrt N - \sqrt n - u\} \le e^{-u^2/2}$.
--
--   **Formalization Note.** `sMin A` is the infimum of $\sqrt{(Ax)\cdot(Ax)}$ over the subtype $\{x \mid x\cdot x = 1\}$ and `frobNorm` is $\sqrt{\sum_{i,j} A_{ij}^2}$. No hypothesis on $n$ is needed: for $n = 0$ both sides of the inequality reduce to $0 \le \|A-B\|_F$.
-- source:
--   standard fact: for real $N\times n$ matrices, $|\sigma_{\min}(A)-\sigma_{\min}(B)|\le\|A-B\|_{op}\le\|A-B\|_F$ (Weyl's perturbation inequality for singular values); used in R. Vershynin, High-Dimensional Probability (Cambridge, 2018), proof of Corollary 7.3.3

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem sMin_lipschitz {N n : ℕ} (A B : Matrix (Fin N) (Fin n) ℝ) :
    |sMin A - sMin B| ≤ frobNorm (A - B) := by sorry

end GaussianMatrix
