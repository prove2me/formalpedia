-- Prove2me | Theorems.Thm_HighDimProb_RandomProcesses_slepian_functional_linear
-- name    : HighDimProb.RandomProcesses.slepian_functional_linear
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-02T08:26:48.209461+00:00
-- url     : https://prove2.me/theorems/8c064f4e-1f10-45a8-8095-04cec093686a
-- title:
--   Functional Slepian comparison for linear Gaussian images
-- statement:
--   Let $G\in\mathbb R^{n+1}$ have independent standard normal coordinates, and let $L,M:\mathbb R^{n+1}\to\mathbb R^m$ be linear maps using disjoint Gaussian coordinates: for every standard basis vector $e_k$, either $Le_k=0$ or $Me_k=0$. Thus $LG$ and $MG$ are independent centered Gaussian vectors. Suppose the corresponding diagonal Gram entries are equal and the Gram matrices satisfy
--
--   $$(MM^\mathsf T)_{ii}=(LL^\mathsf T)_{ii},\qquad
--   (MM^\mathsf T)_{ij}\le(LL^\mathsf T)_{ij}.$$
--
--   Let $f:\mathbb R^m\to\mathbb R$ be twice continuously differentiable, with $f$, $Df$ and $D^2f$ uniformly bounded. If all off-diagonal mixed second derivatives of $f$ are nonnegative, then
--
--   $$\mathbb E[f(MG)]\le\mathbb E[f(LG)].$$
--
--   This is the smooth functional comparison at the center of Slepian's proof, in the linear-image representation used for independent copies. The matrices may be singular. Zero output dimension is allowed. Boundedness makes the expectations and differentiation under them well-defined.
-- source:
--   Vershynin, High-Dimensional Probability (first edition), Lemma 7.2.8, pp. 164–165 (PDF pp. 172–173). Independent linear-image form with explicit bounded smoothness assumptions. https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf.

import Mathlib
open MeasureTheory ProbabilityTheory

theorem HighDimProb.RandomProcesses.slepian_functional_linear {m n : ℕ}
    (L M : (Fin (n + 1) → ℝ) →L[ℝ] (Fin m → ℝ))
    (hindep : ∀ k : Fin (n + 1), L (Pi.single k 1) = 0 ∨ M (Pi.single k 1) = 0)
    (hdiag : ∀ i : Fin m, (∑ k : Fin (n + 1), (L (Pi.single k 1) i) ^ 2) =
      ∑ k : Fin (n + 1), (M (Pi.single k 1) i) ^ 2)
    (hcov : ∀ i j : Fin m,
      (∑ k : Fin (n + 1), M (Pi.single k 1) i * M (Pi.single k 1) j) ≤
        ∑ k : Fin (n + 1), L (Pi.single k 1) i * L (Pi.single k 1) j)
    (f : (Fin m → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) {C D H : ℝ}
    (hf_bound : ∀ y, ‖f y‖ ≤ C)
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (hpositive : ∀ y (i j : Fin m), i ≠ j →
      0 ≤ (fderiv ℝ (fderiv ℝ f) y (Pi.single i 1)) (Pi.single j 1)) :
    (∫ x, f (M x) ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) ≤
      ∫ x, f (L x) ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by sorry
