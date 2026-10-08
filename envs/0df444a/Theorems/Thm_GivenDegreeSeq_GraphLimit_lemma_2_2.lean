-- Prove2me | Theorems.Thm_GivenDegreeSeq_GraphLimit_lemma_2_2
-- name    : GivenDegreeSeq.GraphLimit.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:28.79998+00:00
-- url     : https://prove2.me/theorems/596011c3-de8c-4816-9338-256d27fd7c6c
-- title:
--   Lemma 2.2 — $|\varphi(x)-\varphi(y)|_1\le 2e^{2K}|x-y|_1$ when $|x|_\infty,|y|_\infty\le K$
-- statement:
--   Let $d\in\mathbb R^n$ and let $\varphi$ be the map of (4)–(5). Let $x,y\in\mathbb R^n$ and $K\in\mathbb R$ with $\max\{|x|_\infty,|y|_\infty\}\le K$. Then
--   $$|\varphi(x)-\varphi(y)|_1\le 2e^{2K}\,|x-y|_1,$$
--   where $|z|_1=\sum_i|z_i|$ is the $L^1$ norm and $|z|_\infty=\max_i|z_i|$.
--
--   This Lipschitz bound in $L^1$ is the technical input that lets the proof of Theorem 1.1 control the iterates $x_\ell=\varphi(x_{\ell-1})$ in the $L^1$ norm, eq. (26).
--
--   **Formalization Note** $|\cdot|_\infty$ is Mathlib's norm on `Fin n → ℝ`; the $L^1$ norms are written as explicit sums. No positivity of $d$ is assumed: $\log d_i$ cancels in each coordinate of $\varphi(x)-\varphi(y)$.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 14, Lemma 2.2

import Mathlib
import Definitions.Def_GivenDegreeSeq_GraphLimit_Phi

namespace GivenDegreeSeq.GraphLimit

/-- **Lemma 2.2** (Chatterjee–Diaconis–Sly, arXiv:1005.1136v5, p. 14). Let `x, y ∈ ℝⁿ` with
`max{|x|∞, |y|∞} ≤ K`. Then `|φ(x) − φ(y)|₁ ≤ 2e^{2K} |x − y|₁`, where `|·|₁` is the `L¹` norm on
`ℝⁿ`. Here `‖·‖` on `Fin n → ℝ` is the sup norm `|·|∞`; the `L¹` norms are written out as sums.
The terms `log d_i` cancel in `φ(x) − φ(y)`, so no condition on `d` is needed. -/
theorem lemma_2_2 (n : ℕ) (d x y : Fin n → ℝ) (K : ℝ) (hx : ‖x‖ ≤ K) (hy : ‖y‖ ≤ K) :
    ∑ i, |phi d x i - phi d y i| ≤ 2 * Real.exp (2 * K) * ∑ i, |x i - y i| := by sorry

end GivenDegreeSeq.GraphLimit
