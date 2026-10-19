-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_eLpNorm_gradient_convolution_le
-- name    : HunterPDE.Sobolev.eLpNorm_gradient_convolution_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-18T17:35:21.829834+00:00
-- url     : https://prove2.me/theorems/e3624ac7-4e92-418a-90d7-2ca0666f6f61
-- title:
--   Probability mollification contracts the homogeneous weak gradient norm
-- statement:
--   Let $f$ be locally integrable on Euclidean space and have weak first partial derivatives in $L^p$, where $1\le p<\infty$. For every nonnegative smooth compactly supported kernel $\rho$ of integral one,
--   $$\|D(\rho*f)\|_{L^p}\le \||Df|\|_{L^p}.$$
--   The right side uses the Euclidean length of the selected weak partial derivatives. No global $L^p$ membership of $f$ is required. The statement includes dimension zero, with local integrability specified separately. This is the fixed-kernel homogeneous version of the usual Sobolev mollification estimate; it follows by commutation with weak derivatives, the triangle inequality for the vector integral, and scalar Young contraction. It is an open prerequisite, not a claim of an established proof.
-- source:
--   Hunter, Notes on Partial Differential Equations (2014), https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, printed p.55 Theorem 3.19 (commutation), and printed p.70 proof of Theorem 3.37 (mollification). Fixed-kernel homogeneous generalization of those arguments; scalar Young estimate from printed p.9 Theorem 1.23, https://www.math.ucdavis.edu/~hunter/pdes/ch1.pdf. Euclidean vector norm retained before applying Young, so no dimension factor is introduced.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
open MeasureTheory ContinuousLinearMap
open scoped Convolution ENNReal

theorem HunterPDE.Sobolev.eLpNorm_gradient_convolution_le {n : ℕ} {p : ENNReal}
    (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hloc : LocallyIntegrable f volume)
    (hf : ∀ i : Fin n, ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      HunterPDE.Shared.HasWeakDeriv Set.univ (Pi.single i 1) f g ∧ MemLp g p volume)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ : HunterPDE.Shared.IsTestFunction Set.univ ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1) :
    eLpNorm (fun x => ‖gradient (ρ ⋆[lsmul ℝ ℝ, volume] f) x‖) p volume ≤
      eLpNorm (HunterPDE.Shared.weakGradNorm Set.univ f) p volume := by sorry
