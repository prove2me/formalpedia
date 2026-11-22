-- Prove2me | Theorems.Thm_MasulloAudit_truncated_convolution_not_compact
-- name    : MasulloAudit.truncated_convolution_not_compact
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:29:56.812032+00:00
-- url     : https://prove2.me/theorems/e7158823-4312-4d73-b4de-ae59151258d3
-- title:
--   Truncated convolution $\mathbf 1_{\{n\le 0\}}\cdot(a*x)$ on $\ell^2(\mathbb Z)$ is not compact
-- statement:
--   Let $\ell^2(\mathbb Z)$ be the Hilbert space of square-summable complex sequences $x=(x_n)_{n\in\mathbb Z}$. Let $a=(a_k)_{k\in\mathbb Z}$ be a finitely supported complex sequence (only finitely many $a_k\neq 0$), and consider the truncated convolution operator $\mathrm{TC}_a:\ell^2(\mathbb Z)\to\ell^2(\mathbb Z)$,
--   $$
--   (\mathrm{TC}_a x)_n=\begin{cases}\displaystyle\sum_{k\in\mathbb Z} a_k\,x_{n-k}, & n\le 0,\\[4pt] 0, & n>0,\end{cases}
--   \qquad\text{i.e.}\qquad \mathrm{TC}_a=T_{\le 0}\circ\sum_k a_k S_k ,
--   $$
--   where $S_k$ is the shift $(S_kx)_n=x_{n-k}$ and $T_{\le0}$ is the truncation to indices $n\le 0$ (equivalently $\mathrm{TC}_a x=\mathbf 1_{\{n\le 0\}}\cdot(a*x)$).
--
--   **Theorem.** If $a\neq 0$, then
--   $$
--   \mathrm{TC}_a \text{ is not a compact operator on } \ell^2(\mathbb Z).
--   $$
--
--   The convolution part $x\mapsto a*x$ is translation-invariant, and cutting it off on only one side, to the half-line $n\le 0$, still leaves an infinite-dimensional region on which the operator acts like a nonzero convolution. Hence a one-sided cutoff cannot turn a convolution operator into a compact (in particular trace-class) operator; two-sided localisation is needed for that.
--
--   **Formalization Note.** This is the discrete $\ell^2(\mathbb Z)$ analogue of the half-line convolution $M_{1_{(-\infty,L]}}\circ(f*\cdot)$ on $L^2(\mathbb R)$, whose non-compactness shows that a one-sided multiplicative cutoff does not regularize the convolution action. The operators come from the platform definition `Definitions.Def_MasulloAudit_TruncConv`: $\ell^2(\mathbb Z)$ is `L2Z := lp (fun _ : ℤ => ℂ) 2`, $a$ is a finitely supported function `a : ℤ →₀ ℂ`, and $\mathrm{TC}_a$ is `truncConv a : L2Z →L[ℂ] L2Z`. Compactness is Mathlib's `IsCompactOperator`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, footnote 2 on p. 514 and the operator R_ρ A_φ̃ = P_{ρ,λ} ∘ A_φ̃ ∘ P̂_{ρ,λ′} on pp. 516-517; cf. A. Connes, Selecta Math. 5 (1999), §VII.

import Definitions.Def_MasulloAudit_TruncConv
import Mathlib.Analysis.Normed.Operator.Compact.Basic

namespace MasulloAudit

theorem truncated_convolution_not_compact (a : ℤ →₀ ℂ) (ha : a ≠ 0) :
    ¬ IsCompactOperator (truncConv a) := by sorry

end MasulloAudit
