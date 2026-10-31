-- Prove2me | Theorems.Thm_OgawaNagaoka_lemma5_trace_derivative
-- name    : OgawaNagaoka.lemma5_trace_derivative
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:34.185834+00:00
-- url     : https://prove2.me/theorems/94469cc5-8fec-4d0d-b75e-d8881430211e
-- title:
--   Lemma 5: $\frac{\partial}{\partial t}\mathrm{Tr}f(X(t))=\mathrm{Tr}f'(X(t))\frac{\partial X(t)}{\partial t}$
-- statement:
--   Let $f:(a,b)\to\mathbb R$ be analytic and let $X(t)$ be a Hermitian operator on a finite-dimensional space depending on a real parameter $t$, with spectrum in $(a,b)$. Then
--
--   $$
--   \frac{\partial}{\partial t}\mathrm{Tr}\,f(X(t))=\mathrm{Tr}\,f'(X(t))\frac{\partial X(t)}{\partial t},
--   $$
--
--   where $f'$ is the derivative of $f$. The identity is used to differentiate $f(\pi)$ in the proof of Lemma 2 and $E_0(s,\pi)$ in the proof of (16).
--
--   The statement is at a point $t_0$: if $X(t)$ is Hermitian with spectrum in $(a,b)$ for $t$ near $t_0$ and $X$ is differentiable at $t_0$ with derivative $X'$, then $t\mapsto\mathrm{Tr}f(X(t))$ is differentiable at $t_0$ with derivative $\mathrm{Tr}\,f'(X(t_0))X'$.
--
--   Differences from the source:
--   - generalization: $X(t)$ Hermitian with spectrum in $(a,b)$ for every $t$ → only for $t$ in a neighbourhood of the point $t_0$ where the derivative is taken; reason: if the hypothesis holds for every $t$ it holds near every $t_0$, so the paper's statement follows at every $t$
--   - reading: $\partial X(t)/\partial t$ (differentiability of $X$ implicit) → entrywise `HasDerivAt (fun t => X t i j) (X' i j) t₀`; reason: the derivative of $X$ appears in the conclusion, so the source assumes $X$ differentiable; for matrices entrywise differentiability is differentiability
--   - encoding: operators, $f(X)$, $\mathrm{Tr}$ → square complex matrices over a finite type, `cfc f X`, complex `Matrix.trace`; reason: finite-dimensional operators are matrices and $f(X)$ of a Hermitian $X$ is defined by the functional calculus
--   - encoding: the conclusion as an equation of derivatives → `HasDerivAt (fun t => (cfc f (X t)).trace) ((cfc (deriv f) (X t₀) * X').trace) t₀`; reason: asserts both that the derivative exists and its value
--   - encoding: $f : (a,b)\to\mathbb R$ analytic, $f'$ its derivative → `f : ℝ → ℝ` with `AnalyticOnNhd ℝ f (Set.Ioo a b)` (real `a`, `b`), $f'$ = `deriv f`; reason: any function on $(a,b)$ extends to $\mathbb R$; `cfc f (X t)` and `deriv f` on the spectrum use only the values of $f$ on $(a,b)$; the spectrum near $t_0$ is bounded, so real endpoints lose no instance
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, Appendix, Lemma 5, p.9

import Mathlib

open Filter Topology

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, Appendix, Lemma 5, p.9: let `f : (a, b) → ℝ` be analytic and `X(t)` a
Hermitian operator depending on a real parameter `t` with spectrum in `(a, b)`. Then
`∂/∂t Tr f(X(t)) = Tr f′(X(t)) ∂X(t)/∂t`.

**Formalization Note.** Operators are matrices indexed by a finite type; `f(X)` is `cfc f X`.
The derivative is taken at a point `t₀`: `X` is Hermitian with spectrum in `(a, b)` for all `t`
near `t₀`, and differentiable at `t₀` entrywise with derivative `X'` (`∂X/∂t`). The conclusion is
that `t ↦ Tr f(X(t))` (complex trace) has derivative `Tr f′(X(t₀)) X'` at `t₀`, with
`f′ = deriv f`. -/
theorem lemma5_trace_derivative {ι : Type} [Fintype ι] [DecidableEq ι] (f : ℝ → ℝ) (a b : ℝ)
    (hf : AnalyticOnNhd ℝ f (Set.Ioo a b)) (X : ℝ → Matrix ι ι ℂ) (X' : Matrix ι ι ℂ) (t₀ : ℝ)
    (hX : ∀ᶠ t in 𝓝 t₀, (X t).IsHermitian ∧ spectrum ℝ (X t) ⊆ Set.Ioo a b)
    (hX' : ∀ i j, HasDerivAt (fun t => X t i j) (X' i j) t₀) :
    HasDerivAt (fun t => (cfc f (X t)).trace) ((cfc (deriv f) (X t₀) * X').trace) t₀ := by sorry

end OgawaNagaoka
