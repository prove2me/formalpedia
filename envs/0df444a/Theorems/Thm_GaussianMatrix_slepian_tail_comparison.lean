-- Prove2me | Theorems.Thm_GaussianMatrix_slepian_tail_comparison
-- name    : GaussianMatrix.slepian_tail_comparison
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T08:01:02.80003+00:00
-- url     : https://prove2.me/theorems/0d7b7c24-dfe4-4afb-802c-78f381a5851a
-- title:
--   Slepian's inequality: equal variances and dominated increments imply $\mathbb P(\max_t X_t>\tau)\le\mathbb P(\max_t Y_t>\tau)$ for centered Gaussian vectors
-- statement:
--   Let $\iota$ be a finite index set. Let $X=(X_t)_{t\in\iota}$ be a random vector on a probability space $(\Omega,P)$ and $Y=(Y_t)_{t\in\iota}$ one on a probability space $(\Omega',Q)$. Assume both are centered and jointly Gaussian: the laws of $\omega\mapsto(X_t(\omega))_{t}$ and $\omega'\mapsto(Y_t(\omega'))_{t}$ are Gaussian measures on $\mathbb R^\iota$, and $\mathbb E X_t=\mathbb E Y_t=0$ for every $t$. Suppose that the variances agree and that the increments of $X$ are dominated by those of $Y$:
--   $$\mathbb E\,X_t^2=\mathbb E\,Y_t^2,\qquad \mathbb E\,(X_s-X_t)^2\le\mathbb E\,(Y_s-Y_t)^2\qquad\text{for all } s,t\in\iota .$$
--   Then for every threshold $\tau\in\mathbb R$,
--   $$P\Big(\max_{t\in\iota}X_t>\tau\Big)\;\le\;Q\Big(\max_{t\in\iota}Y_t>\tau\Big).$$
--   Equivalently, with equal variances the hypothesis says $\mathbb E X_sX_t\ge\mathbb E Y_sY_t$: the more strongly correlated vector $X$ has a stochastically smaller maximum.
--
--   This is Slepian's inequality, the comparison principle that Tropp and Webber use in the proof of Lemma B.1 of arXiv:2306.12418. There it is applied to $X_{u,v}=\langle S^{*}u,GTv\rangle+\|S^{*}u\|\|Tv\|\gamma$ and $Y_{u,v}=\|S^{*}u\|\langle h,Tv\rangle+\|Tv\|\langle g,S^{*}u\rangle$. The scalar Gaussian $\gamma$ is added to equalize the variances. This gives the sharp second-moment Chevet bound $\mathbb E\|SGT\|^2\le(\|S\|\|T\|_F+\|S\|_F\|T\|)^2$. Unlike the Sudakov–Fernique inequality, which needs no variance condition, it compares whole distributions of the maxima and not just their expectations. So it controls every moment $\mathbb E(\max X)_+^q$.
--
--   **Formalization Note.** Joint Gaussianity is expressed with Mathlib's `HasGaussianLaw` for the vector map $\omega\mapsto(t\mapsto X_t(\omega))$ into `ι → ℝ`. This also forces $P$ and $Q$ to be probability measures. Means, variances and increments are written as Bochner integrals; Gaussian coordinates are square-integrable, so these are the true moments. The maximum is `⨆ t, X t ω`, a genuine maximum for finite nonempty $\iota$. For empty $\iota$ both maxima equal $0$ (the real convention $\sup\emptyset=0$), and the two sides coincide, since both are probability measures evaluated on $\{0>\tau\}$. The strict-inequality form stated here is equivalent to the form $P(\max X\ge\tau)\le Q(\max Y\ge\tau)$ found in textbooks, by monotone limits in $\tau$. The two vectors may live on different probability spaces; no coupling is assumed.
-- source:
--   R. Vershynin, High-Dimensional Probability (Cambridge Univ. Press, 2018), Section 7.2, Theorem 7.2.1 (Slepian's inequality), stated there for mean-zero Gaussian processes with E X_t^2 = E Y_t^2 and E(X_t-X_s)^2 <= E(Y_t-Y_s)^2, conclusion P(sup X >= tau) <= P(sup Y >= tau); theorem number from memory, cited by Tropp-Webber (arXiv:2306.12418, proof of Lemma B.1) as [105, Sec. 7.2]. Original: D. Slepian, 'The one-sided barrier problem for Gaussian noise', Bell System Tech. J. 41 (1962), 463-501.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem slepian_tail_comparison {ι Ω Ω' : Type*} [Fintype ι] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'} (X : ι → Ω → ℝ) (Y : ι → Ω' → ℝ)
    (hX : HasGaussianLaw (fun ω t => X t ω) P) (hY : HasGaussianLaw (fun ω t => Y t ω) Q)
    (hX0 : ∀ t, ∫ ω, X t ω ∂P = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂Q = 0)
    (hvar : ∀ t, ∫ ω, X t ω ^ 2 ∂P = ∫ ω, Y t ω ^ 2 ∂Q)
    (hinc : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂P ≤ ∫ ω, (Y s ω - Y t ω) ^ 2 ∂Q) (τ : ℝ) :
    P {ω | τ < ⨆ t, X t ω} ≤ Q {ω | τ < ⨆ t, Y t ω} := by sorry

end GaussianMatrix
