-- Prove2me | Theorems.Thm_MeanVarASD_AFSD_sandwich
-- name    : MeanVarASD.AFSD.sandwich
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:34.081501+00:00
-- url     : https://prove2.me/theorems/b1bc0ef0-46b9-4494-93da-2cd9b260e0f9
-- title:
--   Proof of Theorem 7, p. 7 — u_L(x;δ) ≤ u(x) ≤ u_U(x;δ) for u(δ) = 0 and γ ≤ u′ ≤ 1
-- statement:
--   Let $\gamma,\delta\in\mathbb R$ and let $u:\mathbb R\to\mathbb R$ be differentiable with $u(\delta)=0$ and $\gamma\le u'(x)\le1$ for all $x$. Then for every $x$,
--   $$u_L(x;\delta)\le u(x)\le u_U(x;\delta),$$
--   where
--   $$u_U(x;\delta)=\gamma(x-\delta)+(1-\gamma)(x-\delta)_+=\begin{cases}\gamma(x-\delta)&x\le\delta,\\ x-\delta&x>\delta,\end{cases}\qquad u_L(x;\delta)=\gamma(x-\delta)-(1-\gamma)(\delta-x)_+=\begin{cases}x-\delta&x\le\delta,\\ \gamma(x-\delta)&x>\delta.\end{cases}$$
--
--   The two piecewise-linear functions are the extreme normalized utilities; the proof of Theorem 7 compares $\mathbb E\,u_U(X;\delta)$ with $\mathbb E\,u_L(Y;\delta)$.
--
--   **Formalization Note** The statement holds for every real $\gamma$ (the hypotheses force $\gamma\le1$); in the paper $\gamma\in(0,1]$.
-- source:
--   Müller, Scarsini, Tsetlin & Winkler, Ranking distributions when only means and variances are known, INSEAD Working Paper 2020/36/DSC (31 July 2020; SSRN 3440103), p. 7 (PDF 8), proof of Theorem 7, definitions of u_U and u_L

import Mathlib
import Definitions.Def_MeanVarASD_AFSD_Defs

namespace MeanVarASD.AFSD

/-- Proof of Theorem 7, p. 7: a differentiable `u` with `u(δ) = 0` and `γ ≤ u′ ≤ 1` satisfies
`u_L(x; δ) ≤ u(x) ≤ u_U(x; δ)` for every `x`. -/
theorem sandwich (γ δ : ℝ) (u : ℝ → ℝ) (hu : Differentiable ℝ u) (hδ : u δ = 0)
    (hu' : ∀ x, γ ≤ deriv u x ∧ deriv u x ≤ 1) :
    ∀ x, uL γ δ x ≤ u x ∧ u x ≤ uU γ δ x := by sorry

end MeanVarASD.AFSD
