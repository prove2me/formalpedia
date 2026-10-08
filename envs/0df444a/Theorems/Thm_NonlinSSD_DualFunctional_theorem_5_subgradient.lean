-- Prove2me | Theorems.Thm_NonlinSSD_DualFunctional_theorem_5_subgradient
-- name    : NonlinSSD.DualFunctional.theorem_5_subgradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:24:06.846371+00:00
-- url     : https://prove2.me/theorems/941a84e4-45e5-4609-a2bd-3bc62d2f3970
-- title:
--   Theorem 5 (with X ∈ [a, b] a.s.) — (P_X, −X) is a subgradient of f(v, ζ) = −E v^*(ζ) at (v̄, ζ̄)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $a\le b$, $\bar v\in\mathcal U_1([a,b])$, and $\bar\zeta\in\mathcal L_1$ with $0\le\bar\zeta\le\bar v'_-(a)$ almost surely. Let $f(v,\zeta)=-\mathbb E\,v^*(\zeta)\in(-\infty,+\infty]$ be the functional (35) on $\mathrm{Lip}(\mathbb R)\times\mathcal L_1$. Let $X$ be a measurable selection
--   $$X(\omega)\in\operatorname*{argmax}_{t}\,[\bar v(t)-\bar\zeta(\omega)t]\quad\text{a.s., with } X\in[a,b]\ \text{a.s.},$$
--   and let $P_X$ be the law of $X$. Then:
--
--   1. $f(\bar v,\bar\zeta)$ is finite;
--   2. for every Lipschitz continuous $v:\mathbb R\to\mathbb R$ and every $\zeta\in\mathcal L_1$,
--   $$f(v,\zeta)\ \ge\ f(\bar v,\bar\zeta)+\int\big(v(t)-\bar v(t)\big)\,dP_X(t)-\mathbb E\big[X(\zeta-\bar\zeta)\big];$$
--   3. $X\in\mathcal L_\infty$;
--   4. for every $v$ that is Lipschitz with constant $K$,
--   $$\int|v(t)|\,dP_X(t)\le\big(|v(0)|+K\big)\big(1+\mathbb E|X|\big).$$
--
--   Items 3 and 4 say that $(P_X,-X)$ acts as a continuous linear functional on $\mathrm{Lip}(\mathbb R)\times\mathcal L_1$ (with the norm $\|v\|_{\mathrm{Lip}}=|v(0)|+\sup_{t\ne s}|v(t)-v(s)|/|t-s|$), so together with item 2 it is a subgradient of $f$ at $(\bar v,\bar\zeta)$, and $f$ is subdifferentiable there. This supplies the subgradients that a nonsmooth method for the dual problem needs.
--
--   **Formalization Note** The paper states the subgradient inequality for *every* measurable selection of the argmax. That is too strong: where $\bar\zeta(\omega)=0$ the argmax contains $[b,\infty)$, and a selection can then fail to be integrable (e.g. $a=-1$, $b=0$, $\bar v(t)=\min(t,0)$, $\bar\zeta=0$, $\Omega=[0,1]$ with Lebesgue measure, $X(\omega)=1/\omega$), so $\mathbb E[X(\zeta-\bar\zeta)]$ is undefined. The paper's proof uses "The selection $X$ is included in $[a,b]$ a.s.", which holds for the selection constructed on p. 13; the hypothesis $X\in[a,b]$ a.s. is added. The printed "$f((\bar v,\bar\zeta)$" is read as $f(\bar v,\bar\zeta)$. $f$ is `EReal`-valued, equal to $+\infty$ ($\top$) unless $v^*(\zeta)$ is a.s. finite with integrable real part; then the inequality is trivial, as in the paper. $\int(v-\bar v)\,dP_X$ is the integral against the pushforward `P.map X`.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), pp. 13–14, Eq. (35), Theorem 5

import Mathlib
import Definitions.Def_NonlinSSD_DualFunctional_Basic

open MeasureTheory

namespace NonlinSSD.DualFunctional

theorem theorem_5_subgradient {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (a b : ℝ) (hab : a ≤ b)
    (vbar : ℝ → ℝ) (hvbar : vbar ∈ NonlinSSD.Optimality.U1 a b) (ζbar : Ω → ℝ) (hζbar : Integrable ζbar P)
    (hζbar_dom : ∀ᵐ ω ∂P, 0 ≤ ζbar ω ∧ ζbar ω ≤ leftDeriv vbar a)
    (X : Ω → ℝ) (hXm : Measurable X) (hXab : ∀ᵐ ω ∂P, X ω ∈ Set.Icc a b)
    (hXmax : ∀ᵐ ω ∂P, ∀ t : ℝ, vbar t - ζbar ω * t ≤ vbar (X ω) - ζbar ω * X ω) :
    fFun P vbar ζbar ≠ ⊤ ∧
    (∀ (v : ℝ → ℝ), (∃ K, LipschitzWith K v) → ∀ (ζ : Ω → ℝ), Integrable ζ P →
      fFun P v ζ ≥ fFun P vbar ζbar +
        ((∫ t, (v t - vbar t) ∂(P.map X) - ∫ ω, X ω * (ζ ω - ζbar ω) ∂P : ℝ) : EReal)) ∧
    MemLp X ⊤ P ∧
    (∀ (v : ℝ → ℝ) (K : NNReal), LipschitzWith K v →
      ∫ t, |v t| ∂(P.map X) ≤ (|v 0| + K) * (1 + ∫ ω, |X ω| ∂P)) := by sorry

end NonlinSSD.DualFunctional
