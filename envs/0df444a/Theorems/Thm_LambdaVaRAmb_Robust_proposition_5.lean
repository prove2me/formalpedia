-- Prove2me | Theorems.Thm_LambdaVaRAmb_Robust_proposition_5
-- name    : LambdaVaRAmb.Robust.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:16:44.601779+00:00
-- url     : https://prove2.me/theorems/8f24f72c-c212-459c-bf2d-c5052c0dd188
-- title:
--   Proposition 5 (formula) — the upper probability of the φ-divergence ball is ℚ̄(A) = g_{φ,δ}(ℙ(A))
-- statement:
--   Let $\mathbb P$ be a probability measure on $(\Omega,\mathcal F)$, let $\phi:[0,\infty)\to\mathbb R\cup\{\infty\}$ be convex with $\phi(1)=0$ and $\phi(0)=\lim_{x\downarrow0}\phi(x)$, and let $\delta>0$. Let $\mathcal P_\phi(\mathbb P,\delta)$ be the set of probability measures $\mathbb Q\ll\mathbb P$ with $D_\phi(\mathbb Q\|\mathbb P)=\mathbb E^{\mathbb P}[\phi(\mathrm d\mathbb Q/\mathrm d\mathbb P)]\le\delta$, and $\overline{\mathbb Q}(A)=\sup_{\mathbb Q\in\mathcal P_\phi(\mathbb P,\delta)}\mathbb Q(A)$. Then for every $A\in\mathcal F$,
--   $$\overline{\mathbb Q}(A)=g_{\phi,\delta}(\mathbb P(A)),$$
--   where $g_{\phi,\delta}(0)=0$, $g_{\phi,\delta}(1)=1$ and, for $x\in(0,1)$,
--   $$g_{\phi,\delta}(x)=\sup\{t\in[x,1]: x\phi(t/x)+(1-x)\phi((1-t)/(1-x))\le\delta\}.$$
--
--   The worst-case probability of an event over a $\phi$-divergence ball therefore depends on the event only through its reference probability, via an explicit distortion function. Combined with Corollary 1 this turns the robust $\Lambda$VaR into a $\Lambda$VaR under the distorted probability $g_{\phi,\delta}\circ\mathbb P$.
--
--   **Formalization Note** $\phi$ may take the value $+\infty$; it is an `EReal`-valued function whose values at negative arguments are never used. The supremum defining $\overline{\mathbb Q}$ is a real supremum over a nonempty set ($\mathbb P$ itself lies in the ball) of values in $[0,1]$.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 11, Proposition 5 (first sentence); proof p. 32

import Mathlib
import Definitions.Def_LambdaVaRAmb_Robust_Setting

namespace LambdaVaRAmb.Robust

open MeasureTheory

theorem proposition_5 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (φ : ℝ → EReal) (hφ : IsPhiFunction φ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ A : Set Ω, MeasurableSet A → upperProb (phiBall φ P δ) A = gPhi φ δ (P.real A) := by sorry

end LambdaVaRAmb.Robust
