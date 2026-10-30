-- Prove2me | Theorems.Thm_LindenReversibility_eq_10
-- name    : LindenReversibility.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:17:17.700625+00:00
-- url     : https://prove2.me/theorems/385ab18a-db9c-4a3c-9555-caa8534e16d3
-- title:
--   Eq. (10): Donald's identity
-- statement:
--   Let $\rho_1,\dots,\rho_n$ be density matrices on a finite-dimensional space, $p_1,\dots,p_n\ge0$ with $\sum_k p_k = 1$, $\rho = \sum_k p_k\rho_k$, and let $\sigma$ be any density matrix. Then
--
--   $$
--   \sum_k p_k\,S(\rho_k\|\sigma) = \sum_k p_k\,S(\rho_k\|\rho) + S(\rho\|\sigma),
--   $$
--
--   where $S$ is the relative entropy (9) with values in $[0,+\infty]$. Whenever the paper's form $-S(\rho\|\sigma) = \sum_k p_k\big(S(\rho_k\|\rho) - S(\rho_k\|\sigma)\big)$ is defined, it is this identity.
--
--   In the paper $\rho_k = \rho^{BC}_k$ are Bob and Claire's post-measurement states and $\rho = \rho^{BC}$ by (8); with $\sigma$ the optimal separable state of (11), the identity gives (12) and the first line of (13).
--
--   Differences from the source:
--   - encoding: −S(ρ‖σ) = Σ_k p_k (S(ρ_k‖ρ) − S(ρ_k‖σ)), with differences of possibly infinite relative entropies → Σ_k p_k S(ρ_k‖σ) = Σ_k p_k S(ρ_k‖ρ) + S(ρ‖σ) in [0, +∞]; reason: equal to the printed form whenever that is defined (all terms finite), and well defined when S(ρ‖σ) = +∞
--   - generalization: Bob and Claire's states ρ^{BC}_k, ρ^{BC} = Σ p_k ρ^{BC}_k by (8) → any finite family of density matrices on any finite-dimensional space, any weights p_k ≥ 0 summing to 1; reason: the paper's instance is I = B × C with its own p_k, ρ_k; the identity is stated for any ensemble, as the sentence "Simple algebra shows" uses it
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, eq. (10), pp.2–3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_LindenReversibility_relEntropy

open QAlgorithms (IsDensityMatrix)
open scoped ENNReal

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, eq. (10), pp.2–3
(Donald's identity): if `ρ = ∑_k p_k ρ_k` is a convex combination of states and `σ` is any state,
then `−S(ρ‖σ) = ∑_k p_k (S(ρ_k‖ρ) − S(ρ_k‖σ))`.

**Formalization Note.** The relative entropy takes values in `ℝ≥0∞` (`+∞` off support), where
the printed differences may be `∞ − ∞`; the identity is stated in the additive form
`∑_k p_k S(ρ_k‖σ) = ∑_k p_k S(ρ_k‖ρ) + S(ρ‖σ)`, which is the printed one whenever that is
defined. The states live on an arbitrary finite index type `I` (Bob and Claire's `B × C` in the
paper). The outcomes are `Fin n`. -/
theorem eq_10 {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} (p : Fin n → ℝ)
    (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1) (ρk : Fin n → Matrix I I ℂ)
    (hρk : ∀ k, IsDensityMatrix (ρk k)) (ρ : Matrix I I ℂ) (hρ : ρ = ∑ k, (p k : ℂ) • ρk k)
    (σ : Matrix I I ℂ) (hσ : IsDensityMatrix σ) :
    ∑ k, ENNReal.ofReal (p k) * relEntropy (ρk k) σ =
      ∑ k, ENNReal.ofReal (p k) * relEntropy (ρk k) ρ + relEntropy ρ σ := by sorry

end LindenReversibility
