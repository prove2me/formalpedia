-- Prove2me | Theorems.Thm_HunterPDE_Shared_gradient_convolution_ae
-- name    : HunterPDE.Shared.gradient_convolution_ae
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-18T17:51:14.691263+00:00
-- url     : https://prove2.me/theorems/e600eb48-d463-495a-a6f1-d6e6e54193e8
-- title:
--   Mollification commutes with the Euclidean weak gradient
-- statement:
--   Let $f$ be locally integrable on Euclidean space and let $g_i$ be locally integrable weak first partial derivatives. For any smooth compactly supported kernel $\rho$, the classical gradient of $\rho*f$ agrees almost everywhere with the vector integral $\int \rho(y)(g_i(x-y))_i\,dy$. No positivity, normalization, or global integrability is required. The statement includes dimension zero.
-- source:
--   Hunter, Notes on Partial Differential Equations (2014), https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, printed p.55 Theorem 3.19 and its proof. Vector packaging of first-order commutation on the whole space.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
open MeasureTheory ContinuousLinearMap HunterPDE.Shared
open scoped Convolution ContDiff
set_option autoImplicit false

theorem HunterPDE.Shared.gradient_convolution_ae {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hloc : LocallyIntegrable f volume)
    (g : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ∀ i, HasWeakDeriv Set.univ (Pi.single i 1) f (g i))
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : IsTestFunction Set.univ ρ) :
    gradient (ρ ⋆[lsmul ℝ ℝ, volume] f) =ᵐ[volume]
      (fun x => ∫ y, ρ y • (WithLp.toLp 2 (fun i => g i (x-y)) :
        EuclideanSpace ℝ (Fin n))) := by sorry
