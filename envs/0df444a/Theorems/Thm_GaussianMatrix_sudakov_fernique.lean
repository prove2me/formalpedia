-- Prove2me | Theorems.Thm_GaussianMatrix_sudakov_fernique
-- name    : GaussianMatrix.sudakov_fernique
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T07:18:49.244024+00:00
-- url     : https://prove2.me/theorems/e8a1b0d7-f4b4-4f45-896f-4d113c1a435f
-- title:
--   Sudakov–Fernique inequality: dominated increments imply $\mathbb E\max_t X_t\le\mathbb E\max_t Y_t$ for centered Gaussian vectors
-- statement:
--   Let $\iota$ be a finite index set, and let $X=(X_t)_{t\in\iota}$ on a probability space $(\Omega,P)$ and $Y=(Y_t)_{t\in\iota}$ on a probability space $(\Omega',Q)$ be centered, jointly Gaussian random vectors in $\mathbb R^\iota$. That is, the laws of $\omega\mapsto(X_t(\omega))_t$ and $\omega'\mapsto(Y_t(\omega'))_t$ are Gaussian measures on $\mathbb R^\iota$, and $\mathbb E X_t=\mathbb E Y_t=0$ for all $t$. Suppose the increments of $X$ are dominated by those of $Y$:
--   $$\mathbb E\,(X_s-X_t)^2\le\mathbb E\,(Y_s-Y_t)^2\qquad\text{for all } s,t\in\iota .$$
--   Then
--   $$\mathbb E\,\max_{t\in\iota}X_t\;\le\;\mathbb E\,\max_{t\in\iota}Y_t .$$
--
--   This is the Gaussian comparison principle behind the sharp bound $\mathbb E\|G\|\le\sqrt N+\sqrt n$ for an $N\times n$ Gaussian matrix. On a finite net of $S^{n-1}\times S^{N-1}$, one compares $X_{u,v}=\langle Gu,v\rangle$ with $Y_{u,v}=\langle g,u\rangle+\langle h,v\rangle$. Unlike Slepian's lemma, no equality of variances is required.
--
--   **Formalization Note.** Joint Gaussianity is expressed with Mathlib's `HasGaussianLaw` for the vector-valued map $\omega\mapsto(t\mapsto X_t(\omega))$ into `ι → ℝ`; this hypothesis also forces $P$ and $Q$ to be probability measures. The maximum is written `⨆ t, X t ω`, which is a genuine maximum for finite nonempty $\iota$. For empty $\iota$ both sides equal $0$ (the real convention $\sup\emptyset=0$), so the statement remains true. Both maxima are integrable: they are dominated by $\sum_t|X_t|$, and Gaussian coordinates are integrable. The two vectors live on possibly different probability spaces; no independence or coupling is assumed.
-- source:
--   R. Vershynin, High-Dimensional Probability (Cambridge Univ. Press, 2018), Theorem 7.2.11 (Sudakov–Fernique inequality), stated there for mean-zero Gaussian processes; numbering from memory. Originally V. N. Sudakov (1971) and X. Fernique (1975); short proof in S. Chatterjee, 'An error bound in the Sudakov–Fernique inequality', arXiv:math/0510424.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem sudakov_fernique {ι Ω Ω' : Type*} [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} (X : ι → Ω → ℝ) (Y : ι → Ω' → ℝ)
    (hX : HasGaussianLaw (fun ω t => X t ω) P) (hY : HasGaussianLaw (fun ω t => Y t ω) Q)
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂Q = 0)
    (hinc : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂P ≤ ∫ ω, (Y s ω - Y t ω) ^ 2 ∂Q) :
    ∫ ω, (⨆ t, X t ω) ∂P ≤ ∫ ω, (⨆ t, Y t ω) ∂Q := by sorry

end GaussianMatrix
