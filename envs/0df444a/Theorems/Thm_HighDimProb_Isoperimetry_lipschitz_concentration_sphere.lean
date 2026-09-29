-- Prove2me | Theorems.Thm_HighDimProb_Isoperimetry_lipschitz_concentration_sphere
-- name    : HighDimProb.Isoperimetry.lipschitz_concentration_sphere
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-18T05:40:04.892272+00:00
-- url     : https://prove2.me/theorems/bd8a2913-29c6-468b-a903-c4ccb39d8faa
-- title:
--   Theorem 5.1.4 — Concentration of Lipschitz functions on the sphere
-- statement:
--   This is **Theorem 5.1.4**, the concentration-of-measure engine behind the
--   Johnson-Lindenstrauss Lemma: every Lipschitz function of a point drawn uniformly from a
--   high-dimensional Euclidean sphere concentrates tightly around its mean, with a sub-gaussian
--   tail whose rate depends only on the function's Lipschitz constant — not on the ambient
--   dimension $n$.
--
--   There is an absolute constant $C > 0$ such that the following holds. Let
--   $(\Omega, \mathcal F, \mathrm{Prob})$ be a probability space, $n \in \mathbb N$, and let
--   $X : \Omega \to \mathbb R^n$ be a random vector uniformly distributed on the Euclidean
--   sphere of radius $\sqrt n$ (the companion definition `IsUniformOnSphere`). Let
--   $f : \mathbb R^n \to \mathbb R$ be a function that is $L$-Lipschitz on that sphere. Then
--
--   $$
--   \bigl\|f(X) - \mathbb E f(X)\bigr\|_{\psi_2} \;\le\; C L,
--   $$
--
--   where $\|\cdot\|_{\psi_2}$ is the sub-gaussian (Orlicz) norm of the companion definition
--   `subgaussianNorm`. Equivalently, for every $t \ge 0$,
--   $P\{|f(X) - \mathbb E f(X)| \ge t\} \le 2\exp(-ct^2/L^2)$ for an absolute constant $c > 0$.
--
--   The proof (not part of this formalization) compares sub-level sets of $f$ to spherical caps
--   via the isoperimetric inequality on the sphere, reducing the general Lipschitz case to the
--   already-known concentration of *linear* functions of a uniform point.
--
--   **Formalization Note** $f$ is a function on all of $\mathbb R^n$, but the Lipschitz
--   hypothesis (`LipschitzOnWith L f`) and the conclusion only constrain its values on the
--   sphere, matching the book's own domain $f : \sqrt n\,S^{n-1} \to \mathbb R$. The constant
--   $C$ is existentially quantified ahead of every other object, so no numeral is fixed for it;
--   $L$ is a fixed `NNReal` Lipschitz constant supplied as a hypothesis (equivalent to using the
--   Lipschitz seminorm $\|f\|_{\mathrm{Lip}}$ itself, since the bound is monotone in $L$).
-- source:
--   Vershynin, High-Dimensional Probability (2018), Theorem 5.1.4, p. 107 (PDF p. 115)

import Mathlib
import Definitions.Def_HighDimProb_Isoperimetry_SubgaussianNorm
import Definitions.Def_HighDimProb_Isoperimetry_UniformOnSphere

open MeasureTheory

namespace HighDimProb.Isoperimetry

/-- **Theorem 5.1.4** (Concentration of Lipschitz functions on the sphere), Vershynin,
*High-Dimensional Probability* (2018), p. 107.

Consider a random vector `X ∼ Unif(√n Sⁿ⁻¹)`, i.e. `X` is uniformly distributed on the
Euclidean sphere of radius `√n`. Consider a Lipschitz function `f : √n Sⁿ⁻¹ → ℝ`. Then

`‖f(X) − E f(X)‖_{ψ₂} ≤ C ‖f‖_{Lip}`. -/
theorem lipschitz_concentration_sphere :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
        {n : ℕ} (X : Ω → EuclideanSpace ℝ (Fin n)) (hX_meas : Measurable X)
        (hX_unif : IsUniformOnSphere Prob (Real.sqrt n) X)
        (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal)
        (hf_lip : LipschitzOnWith L f (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n))),
        subgaussianNorm Prob (fun ω => f (X ω) - ∫ ω, f (X ω) ∂Prob) ≤ C * (L : ℝ) := by sorry

end HighDimProb.Isoperimetry
