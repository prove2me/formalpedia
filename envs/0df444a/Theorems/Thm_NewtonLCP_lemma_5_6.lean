-- Prove2me | Theorems.Thm_NewtonLCP_lemma_5_6
-- name    : NewtonLCP.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:26.437332+00:00
-- url     : https://prove2.me/theorems/710d98c9-b5f0-4728-ae34-453d8713b0ac
-- title:
--   Lemma 5.6 — bounds on Rump weights
-- statement:
--   For $A\in\mathcal P_\star(\kappa)$ and $H=(I_n+A)^{-1}$, with $Q_H=\mathrm{diag}(q_H)$ the Rump weights and $K=8$,
--
--   $$\|Q_HHv\|_\infty\le\frac{K^2}{2}\sqrt{1+\kappa}\,\|v\|_2\quad\text{for all }v\in\mathbb R^n,\qquad 1_n\le q_H\le\frac K2\sqrt{1+\kappa}\cdot1_n .$$
--
--   The second bound gives $\mathcal N^R(\beta)\subseteq\mathcal N^2(\beta)\subseteq\mathcal N^R(\tfrac K2\sqrt{1+\kappa}\,\beta)$ (12); the $\sqrt{1+\kappa}$ in these bounds is the source of the square-root dependence.
--
--   Differences from the source: none.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Lemma 5.6, p.15 (restated p.18, proof pp.18–19)

import Mathlib
import Definitions.Def_NewtonLCP_Handicap
import Definitions.Def_NewtonLCP_Centrality
import Definitions.Def_NewtonLCP_RumpWeight

open Matrix

namespace NewtonLCP

/-- **Lemma 5.6** (bounding Rump weights). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Lemma 5.6, p.15 (restated p.18, proof
pp.18–19).

For `A ∈ P⋆(κ)` and `H = (Iₙ + A)⁻¹`, with `Q_H = diag(q_H)` as in Definition 5.2:
`‖Q_H H v‖_∞ ≤ (K²/2)√(1+κ)‖v‖₂` for all `v ∈ ℝⁿ`, and `1ₙ ≤ q_H ≤ (K/2)√(1+κ) · 1ₙ`.

**Formalization Note.** `K = 8`; the ∞-norm bound is stated coordinatewise. -/
theorem lemma_5_6 {ι : Type*} [Fintype ι] [DecidableEq ι] (A H : Matrix ι ι ℝ) (κ : ℝ)
    (hA : IsPStarK A κ) (hH : H = (1 + A)⁻¹) :
    (∀ v : ι → ℝ, ∀ i,
      rumpWeight H i * |(H *ᵥ v) i| ≤ 8 ^ 2 / 2 * Real.sqrt (1 + κ) * l2norm v) ∧
    ∀ i, 1 ≤ rumpWeight H i ∧ rumpWeight H i ≤ 8 / 2 * Real.sqrt (1 + κ) := by sorry

end NewtonLCP
