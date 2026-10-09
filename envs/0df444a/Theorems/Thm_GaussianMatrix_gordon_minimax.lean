-- Prove2me | Theorems.Thm_GaussianMatrix_gordon_minimax
-- name    : GaussianMatrix.gordon_minimax
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T07:38:58.85098+00:00
-- url     : https://prove2.me/theorems/0caac3b7-bb3b-4585-829e-a1a01fcc2ba9
-- title:
--   Gordon's minimax comparison inequality: $\mathbb E\min_u\max_t X_{ut}\le\mathbb E\min_u\max_t Y_{ut}$ for centered Gaussian arrays
-- statement:
--   Let $U$ and $T$ be finite index sets. Let $X=(X_{ut})_{u\in U,\,t\in T}$ be a random vector on a probability space $(\Omega,P)$ and $Y=(Y_{ut})_{u\in U,\,t\in T}$ a random vector on a probability space $(\Omega',Q)$. Assume both are centered and jointly Gaussian in $\mathbb R^{U\times T}$: the laws of $\omega\mapsto(X_{ut}(\omega))_{(u,t)}$ and $\omega'\mapsto(Y_{ut}(\omega'))_{(u,t)}$ are Gaussian measures, and $\mathbb E X_{ut}=\mathbb E Y_{ut}=0$ for all $(u,t)$. Assume the increments compare in opposite directions inside and across the blocks $\{u\}\times T$:
--   $$\mathbb E\,(X_{ut}-X_{us})^2\le\mathbb E\,(Y_{ut}-Y_{us})^2\qquad\text{for all }u\in U,\ t,s\in T,$$
--   $$\mathbb E\,(X_{ut}-X_{vs})^2\ge\mathbb E\,(Y_{ut}-Y_{vs})^2\qquad\text{for all }u\neq v\in U,\ t,s\in T.$$
--   Then
--   $$\mathbb E\,\min_{u\in U}\max_{t\in T}X_{ut}\;\le\;\mathbb E\,\min_{u\in U}\max_{t\in T}Y_{ut}.$$
--
--   This is Gordon's minimax comparison inequality, in the form for expectations without an equal-variance assumption. For $|U|=1$ it reduces to the Sudakov–Fernique inequality, and for $|T|=1$ to Sudakov–Fernique applied to $-X$ and $-Y$. Its main application is the sharp lower bound $\mathbb E\,\sigma_{\min}(G)\ge\mathbb E\|h_N\|-\mathbb E\|g_n\|$ for an $N\times n$ standard Gaussian matrix $G$. There one compares $\langle g,u\rangle+\langle h,v\rangle$ (playing the role of $X$) with $\langle Gu,v\rangle$ (playing $Y$) on finite nets $u\in U\subset S^{n-1}$, $v\in T\subset S^{N-1}$. The standard proof uses Gaussian interpolation (Kahane, Chatterjee) applied to the smooth min-max $F_\beta(x)=-\beta^{-1}\log\sum_u\big(\sum_t e^{\beta x_{ut}}\big)^{-1}$. Its mixed second derivatives are $\le0$ inside a block and $\ge0$ across blocks, and $\sum_b\partial_a\partial_bF_\beta=0$.
--
--   **Formalization Note.** Joint Gaussianity is expressed with Mathlib's `HasGaussianLaw` for the map $\omega\mapsto\big((u,t)\mapsto X_{ut}(\omega)\big)$ into `U × T → ℝ`. This forces $P$ and $Q$ to be probability measures. Means and second moments are Bochner integrals; Gaussian coordinates are square-integrable, so no integrability convention intervenes. The min-max is `⨅ u, ⨆ t, X u t ω`, a genuine min-max for nonempty finite $U,T$. If $U$ or $T$ is empty, both sides are $0$ by the real conventions $\inf\emptyset=\sup\emptyset=0$, and the statement remains true. The two vectors may live on different probability spaces, with no coupling assumed.
-- source:
--   Y. Gordon, 'Some inequalities for Gaussian processes and applications', Israel J. Math. 50 (1985), 265-289, Theorem 1.4 (theorem number from memory, not verified; the paper also gives the equal-variance probability form). Textbook statement: R. Vershynin, High-Dimensional Probability (Cambridge Univ. Press, 2018), Exercise 7.2.14 (pp. 167-168) states the equal-variance version, (7.12) is the expectation form, and the remark immediately after it says the equal-variance assumption can be removed for (7.12). See also J.-P. Kahane, 'Une inegalite du type de Slepian et Gordon sur les processus gaussiens', Israel J. Math. 55 (1986), 109-110; Y. Gordon, 'Elliptically contoured distributions', Probab. Th. Rel. Fields 76 (1987), 429-438.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem gordon_minimax {U T Ω Ω' : Type*} [Fintype U] [Fintype T] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    (X : U → T → Ω → ℝ) (Y : U → T → Ω' → ℝ)
    (hX : HasGaussianLaw (fun ω (p : U × T) => X p.1 p.2 ω) P)
    (hY : HasGaussianLaw (fun ω (p : U × T) => Y p.1 p.2 ω) Q)
    (hX0 : ∀ u t, ∫ ω, X u t ω ∂P = 0) (hY0 : ∀ u t, ∫ ω, Y u t ω ∂Q = 0)
    (hsame : ∀ u t s,
      ∫ ω, (X u t ω - X u s ω) ^ 2 ∂P ≤ ∫ ω, (Y u t ω - Y u s ω) ^ 2 ∂Q)
    (hdiff : ∀ u v t s, u ≠ v →
      ∫ ω, (Y u t ω - Y v s ω) ^ 2 ∂Q ≤ ∫ ω, (X u t ω - X v s ω) ^ 2 ∂P) :
    ∫ ω, (⨅ u, ⨆ t, X u t ω) ∂P ≤ ∫ ω, (⨅ u, ⨆ t, Y u t ω) ∂Q := by sorry

end GaussianMatrix
