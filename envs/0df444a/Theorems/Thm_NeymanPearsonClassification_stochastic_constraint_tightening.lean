-- Prove2me | Theorems.Thm_NeymanPearsonClassification_stochastic_constraint_tightening
-- name    : NeymanPearsonClassification.stochastic_constraint_tightening
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T17:43:53.685185+00:00
-- url     : https://prove2.me/theorems/7481535a-5a03-40aa-845c-56c93262d180
-- title:
--   Proposition 4.1: strengthening the constraint costs little type II error
-- statement:
--   Let $\alpha\in(0,1)$ and let $\varphi$ be a continuous convex surrogate. Let $h_1,\dots,h_M$, $M\ge2$, be measurable base classifiers with values in $[-1,1]$, and let $P^-,P^+$ be probability measures. Assume there is $\nu_0>0$ such that $\mathcal H^{\varphi,\alpha-\nu_0}\neq\emptyset$. Then for every $\nu\in(0,\nu_0)$,
--
--   $$\min_{h\in\mathcal H^{\varphi,\alpha-\nu}}R^+_\varphi(h)-\min_{h\in\mathcal H^{\varphi,\alpha}}R^+_\varphi(h)\le\varphi(1)\,\frac{\nu}{\nu_0-\nu}.$$
--
--   So strengthening the constraint on the $\varphi$-type I error by $\nu$ raises the optimal $\varphi$-type II error by at most $O(\nu)$.
--
--   **Formalization Note** The minima are written as infima. Both sets are nonempty because they contain $\mathcal H^{\varphi,\alpha-\nu_0}$, so the infima are the paper's minimal values.
-- source:
--   Rigollet and Tong, Neyman-Pearson classification, convexity and stochastic constraints, arXiv:1102.5750v1 (2011), Section 4.2, Proposition 4.1, p. 9; proof in Section 6.3, pp. 16-17

import Mathlib
import Definitions.Def_NeymanPearsonClassification_Basic

open MeasureTheory ProbabilityTheory

namespace NeymanPearsonClassification

theorem stochastic_constraint_tightening {d M : ℕ} (hM : 2 ≤ M)
    (h : Fin M → EuclideanSpace ℝ (Fin d) → ℝ) (hh : IsBaseFamily h)
    (Pm Pp : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Pm] [IsProbabilityMeasure Pp]
    (φ : ℝ → ℝ) (hφ : IsConvexSurrogate φ)
    (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (ν₀ : ℝ) (hν₀ : 0 < ν₀)
    (hne : (Hphi h Pm φ (α - ν₀)).Nonempty) (ν : ℝ) (hν : ν ∈ Set.Ioo 0 ν₀) :
    minPhiTypeII h Pm Pp φ (α - ν) - minPhiTypeII h Pm Pp φ α ≤ φ 1 * (ν / (ν₀ - ν)) := by sorry

end NeymanPearsonClassification
