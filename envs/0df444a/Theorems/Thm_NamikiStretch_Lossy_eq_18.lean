-- Prove2me | Theorems.Thm_NamikiStretch_Lossy_eq_18
-- name    : NamikiStretch.Lossy.eq_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:32.288981+00:00
-- url     : https://prove2.me/theorems/cb71b454-96c2-4b24-adcb-a2a6b2ab2cec
-- title:
--   (18), p. 3 — displacement covariance of the pure-loss channel: Eη(D(β)ρD†(β)) = D(√ηβ)Eη(ρ)D†(√ηβ)
-- statement:
--   Let $\mathcal E_\eta$ be the pure-loss channel of transmissivity $\eta\in(0,1)$ acting on a single bosonic mode, and let $D(\beta)=e^{\beta a^\dagger-\bar\beta a}$ be the displacement operator. For every density operator $\rho$ and every $\beta\in\mathbb C$,
--   $$\mathcal E_\eta\big(D(\beta)\rho D^\dagger(\beta)\big)=D(\sqrt\eta\,\beta)\,\mathcal E_\eta(\rho)\,D^\dagger(\sqrt\eta\,\beta).$$
--   The statement is made on number-basis matrices: both sides are compared entry by entry, $\langle m|\cdot|n\rangle$ for all $m,n\ge0$, and every series that defines an entry (the two displacement conjugations and the two applications of $\mathcal E_\eta$) converges absolutely.
--
--   Displacement covariance says that a coherent shift before the loss is the same as a shift attenuated by $\sqrt\eta$ after it. It is the ingredient that lets Bob's outcome-dependent displacement be moved through the channel in the teleportation-stretching argument.
--
--   **Formalization Note** $\rho$ is a bounded operator on $\ell^2(\mathbb N)$ satisfying the published density predicate (trace class, self-adjoint, positive, unit trace); $\mathcal E_\eta$ is the published vacuum-loss kernel. The summability of each defining series is part of the conclusion.
-- source:
--   Namiki, Teleportation stretching for single-mode Gaussian channels, arXiv:1603.05292v1, p. 3, (18)

import Mathlib
import Definitions.Def_NamikiStretch_Lossy_Protocol

namespace NamikiStretch.Lossy

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P39
open QAlgorithms.Papers.Independent.Frontier30.P21

theorem eq_18 (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (X : FockOperator) (hX : IsDensity X)
    (β : ℂ) :
    let K : ℕ → ℕ → ℂ := fun m n => X (fockKet n) m
    (∀ a b : ℕ, Summable (dispConjTerm β K a b)) ∧
    (∀ a b : ℕ, Summable (vacuumLossTerm η (dispConj β K) a b)) ∧
    (∀ a b : ℕ, Summable (vacuumLossTerm η K a b)) ∧
    (∀ a b : ℕ, Summable (dispConjTerm (((Real.sqrt η : ℝ) : ℂ) * β) (vacuumLossKernel η K) a b)) ∧
    ∀ m n : ℕ, vacuumLossKernel η (dispConj β K) m n =
      dispConj (((Real.sqrt η : ℝ) : ℂ) * β) (vacuumLossKernel η K) m n := by sorry
end NamikiStretch.Lossy
