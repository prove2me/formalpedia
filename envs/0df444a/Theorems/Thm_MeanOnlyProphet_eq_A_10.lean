-- Prove2me | Theorems.Thm_MeanOnlyProphet_eq_A_10
-- name    : MeanOnlyProphet.eq_A_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:22:10.09733+00:00
-- url     : https://prove2.me/theorems/97edbe6e-1877-4ded-b27e-f733d50d1aab
-- title:
--   (A.10) — $g(\alpha,\xi,z)\le 9/64$
-- statement:
--   For $\alpha\ge1$, $\xi\in[0,1]$ and $z>0$ let $p_*=e^{-\alpha z}(1-\xi+\xi e^{-z})$ and $s=e^{-(\alpha+\xi)z}$. Then
--   $$
--   g(\alpha,\xi,z):=\left(1+\sqrt{1+e^{-z}}\right)\frac{(\alpha+\xi)(p_*-s)}{1-p_*}\ \le\ \frac9{64}.
--   $$
--   This three-variable inequality is the analytic core of Lemma A.9 and the source of the constant $9/64$ in Lemma A.4.
--
--   Differences from the source: none.
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), (A.10), p.35 (PDF p.36)

import Mathlib

namespace MeanOnlyProphet

/-- **Inequality (A.10).** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711
(held version, sha256 c68bfec4…), (A.10), p.35 (PDF p.36), with `p∗ := e^{−αz} · (1 − ξ + ξ · e^{−z})` and
`s := e^{−(α+ξ)·z}`: "g(α, ξ, z) := (1 + √(1 + e^{−z})) · (α + ξ) · (p∗ − s)/(1 − p∗) ≤ 9/64, α ≥ 1,
ξ ∈ [0, 1], z > 0."

A real inequality in three variables; `1 − p∗ > 0` on the stated domain. -/
theorem eq_A_10 (α ξ z : ℝ) (hα : 1 ≤ α) (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) (hz : 0 < z) :
    let pstar := Real.exp (-α * z) * (1 - ξ + ξ * Real.exp (-z))
    let s := Real.exp (-(α + ξ) * z)
    (1 + Real.sqrt (1 + Real.exp (-z))) * ((α + ξ) * (pstar - s) / (1 - pstar)) ≤ 9 / 64 := by sorry

end MeanOnlyProphet
