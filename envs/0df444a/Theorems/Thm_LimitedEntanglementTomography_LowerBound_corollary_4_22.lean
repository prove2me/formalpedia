-- Prove2me | Theorems.Thm_LimitedEntanglementTomography_LowerBound_corollary_4_22
-- name    : LimitedEntanglementTomography.LowerBound.corollary_4_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:45.937485+00:00
-- url     : https://prove2.me/theorems/52d471c3-72db-4329-b772-7e60d7c56c3a
-- title:
--   Corollary 4.22 — log-Sobolev inequality for a Gaussian conditioned on a convex set
-- statement:
--   Let $K\subseteq\mathbb R^s$ be a closed convex set with nonempty interior, let $\kappa>0$, and let
--   $$d\mu_K(x)=\frac1{Z_K}\,e^{-\kappa\|x\|_2^2/2}\,\mathbf 1_K(x)\,dx .$$
--   Every positive smooth function $f:\mathbb R^s\to\mathbb R$ with $\mathbb E_{\mu_K}f=1$ satisfies
--   $$\mathrm{Ent}_{\mu_K}(f)\le\frac1{2\kappa}\,\mathbb E_{\mu_K}\Big[\frac{\|\nabla f\|_2^2}{f}\Big],$$
--   both sides taken in $[0,\infty]$.
--
--   Applied to the prior of §6.1 this gives the log-Sobolev constant $\tau^2/d^3$ that converts Fisher information into mutual information.
--
--   Differences from the source:
--   - encoding: Ent_{μ_K}(f) = E[f log f] − E f log E f and E[‖∇f‖²/f] as real numbers → both sides in [0,∞]; Ent written as E[f log f − f + 1], with E f = 1 given as ∫⁻ f = 1; reason: equal when E f = 1; extended values cover the case of an infinite right-hand side (where the source says there is nothing to prove) with no integrability hypothesis added
--   - encoding: probabilities and expectations of nonnegative quantities in ℝ → values of measures in [0,∞] (ENNReal); reason: a probability is the same number; inequalities are unchanged
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, §4.5, printed p.19 / PDF p.21, Corollary 4.22 (eq. (35))

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Prior

open scoped ENNReal ComplexOrder

/-!
Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, *Tight Lower Bounds for State
Tomography with Limited Entanglement*, STOC 2027 submission #1625 (October 2026), Corollary 4.22, printed p.19 / PDF p.21, eq. (35).
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory ProbabilityTheory Matrix ShadowTomography.ClassicalLB

/-- **Corollary 4.22.** Let `K ⊆ ℝ^s` be closed and convex with nonempty interior, `κ > 0`, and
`dμ_K(x) = Z_K⁻¹ e^{−κ‖x‖²/2} 1_K(x) dx`. Every positive smooth `f` with `E_{μ_K} f = 1` satisfies
`Ent_{μ_K}(f) ≤ (1/(2κ)) E_{μ_K}[‖∇f‖₂² / f]` (both sides in `[0, ∞]`). -/
theorem corollary_4_22 (s : ℕ) (K : Set (Coord s)) (hK : IsClosed K) (hKc : Convex ℝ K)
    (hKi : (interior K).Nonempty) (κ : ℝ) (hκ : 0 < κ) (f : Coord s → ℝ)
    (hf : ∀ x, 0 < f x) (hfs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf1 : ∫⁻ x, ENNReal.ofReal (f x) ∂(truncGauss s κ K) = 1) :
    entropy (truncGauss s κ K) f ≤
      ENNReal.ofReal (1 / (2 * κ)) * fisherFunctional (truncGauss s κ K) f := by sorry

end LimitedEntanglementTomography.LowerBound
