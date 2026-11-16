-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_Supplement_theorem_4_1
-- name    : GaussPolyReg.Approx.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:28:49.325108+00:00
-- url     : https://prove2.me/theorems/37fa3226-4051-44c9-825e-029885c81dc9
-- title:
--   Theorem 4.1 — dimension-independent robust Borell inequality
-- statement:
--   For every $a,s\in(0,1)$ and $\varepsilon>0$, there is $\delta=\delta(a,s,\varepsilon)>0$ such that, in every dimension $n$, every Gaussian-measurable $A\subset\mathbb R^n$ with $\gamma_n(A)=a$ and
--
--   $$\operatorname{Stab}_s(A)\ge\operatorname{Stab}_s(H_a)-\delta,\qquad H_a=(-\infty,\Phi^{-1}(a)),$$
--
--   admits a halfspace $H=\{x:\sum_i c_ix_i\ge t\}$, with $\sum_i c_i^2=1$, satisfying
--
--   $$\gamma_n(H)=a,\qquad\gamma_n(A\triangle H)\le\varepsilon.$$
--
--   The positive tolerance is chosen before the dimension and the event. The halfspace has exactly the same Gaussian measure, and the error is the symmetric-difference measure itself, equivalently the squared $L^2$ indicator error. This is the paper's full nonquantitative robustness statement.
--
--   Differences from the source:
--   - encoding: Gaussian-measurable sets, indicators and expectations → NullMeasurableSet for the Gaussian measure, L² indicator classes and real Gaussian probabilities; reason: includes the completion of the measure and all source events; bounded indicators and L² functions on probability spaces are integrable
--   - encoding: OU noise stability with correlation s on ordinary coordinates and s^r on grade-r coordinates → the concrete joint Gaussian integral of f(X) f(Y), with Y_i = s^(g_i) X_i + sqrt(1-s^(2g_i)) G_i and independent Gaussian X,G; reason: this is the source correlated pair; the equivalent spectral identity remains a proof obligation rather than a defining assumption
--   - encoding: sets and normalized halfspaces in ℝ^n, with Gaussian symmetric-difference measure → Fin n → ℝ, finiteHalfspace c t, and (A \ H) ∪ (H \ A); reason: the finite product Gaussian is exactly γ_n, the affine normal has sum of squares one, and the displayed union is the symmetric difference
--   - encoding: H_a = (−∞, Φ⁻¹(a)) ⊂ ℝ → modelHalfspace a in Fin 1 → ℝ using the published Cohen2019.Robust.PhiInvReal; reason: the identical one-dimensional event and standard Gaussian quantile, evaluated only at 0 < a < 1
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Theorem 4.1, p.13; §2, p.3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Supplement_Noise

open MeasureTheory ProbabilityTheory Filter Topology

namespace GaussPolyReg.Approx.Supplement

/-- Theorem 4.1, p.13. δ is selected before the dimension and event.
The halfspace has exactly measure a and symmetric-difference error at most ε. -/
theorem theorem_4_1 (a s ε : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (A : Set (Fin n → ℝ)),
      NullMeasurableSet A (gaussianProduct (Fin n)) → gaussianMass A = a →
      setStability s (modelHalfspace a) - δ ≤ setStability s A →
      ∃ (c : Fin n → ℝ) (t : ℝ), (∑ i, c i ^ 2) = 1 ∧
        gaussianMass (finiteHalfspace c t) = a ∧
        gaussianMass ((A \ finiteHalfspace c t) ∪ (finiteHalfspace c t \ A)) ≤ ε := by sorry

end GaussPolyReg.Approx.Supplement
