-- Prove2me | Theorems.Thm_NeymanPearsonClassification_gamma_antitone_convex
-- name    : NeymanPearsonClassification.gamma_antitone_convex
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T17:43:06.510751+00:00
-- url     : https://prove2.me/theorems/876954f3-198b-4971-a6f8-f90c57370a7d
-- title:
--   Lemma 6.2: the optimal convexified type II error is non-increasing and convex
-- statement:
--   Let $\varphi$ be a convex surrogate, let $h_1,\dots,h_M$, $M\ge2$, be measurable base classifiers with values in $[-1,1]$, and let $P^-,P^+$ be probability measures. Let
--
--   $$\gamma(a)=\inf_{\mathsf h_\lambda\in\mathcal H^{\varphi,a}}R^+_\varphi(\mathsf h_\lambda).$$
--
--   Then $\gamma$ is a non-increasing convex function on $[0,1]$, where $\gamma=+\infty$ wherever $\mathcal H^{\varphi,a}=\emptyset$.
--
--   **Formalization Note** In Lean $\gamma$ is real-valued, so the statement is made on $D=\{a\in[0,1]:\mathcal H^{\varphi,a}\neq\emptyset\}$: $\gamma$ is non-increasing on $D$, $D$ is convex, and $\gamma$ is convex on $D$. Because $a\mapsto\mathcal H^{\varphi,a}$ is increasing, $D$ is an up-closed subinterval of $[0,1]$, and the statement is equivalent to the paper's statement with $\gamma=+\infty$ off $D$.
-- source:
--   Rigollet and Tong, Neyman-Pearson classification, convexity and stochastic constraints, arXiv:1102.5750v1 (2011), Section 6.3, Lemma 6.2, p. 16

import Mathlib
import Definitions.Def_NeymanPearsonClassification_Basic

open MeasureTheory ProbabilityTheory

namespace NeymanPearsonClassification

theorem gamma_antitone_convex {d M : ℕ} (hM : 2 ≤ M)
    (h : Fin M → EuclideanSpace ℝ (Fin d) → ℝ) (hh : IsBaseFamily h)
    (Pm Pp : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Pm] [IsProbabilityMeasure Pp]
    (φ : ℝ → ℝ) (hφ : IsConvexSurrogate φ) :
    AntitoneOn (minPhiTypeII h Pm Pp φ)
        {a : ℝ | a ∈ Set.Icc (0 : ℝ) 1 ∧ (Hphi h Pm φ a).Nonempty} ∧
      ConvexOn ℝ {a : ℝ | a ∈ Set.Icc (0 : ℝ) 1 ∧ (Hphi h Pm φ a).Nonempty}
        (minPhiTypeII h Pm Pp φ) := by sorry

end NeymanPearsonClassification
