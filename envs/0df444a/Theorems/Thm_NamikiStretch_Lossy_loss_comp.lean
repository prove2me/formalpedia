-- Prove2me | Theorems.Thm_NamikiStretch_Lossy_loss_comp
-- name    : NamikiStretch.Lossy.loss_comp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:38.307547+00:00
-- url     : https://prove2.me/theorems/69a1be9d-fc97-4382-9b8f-22369fa0600c
-- title:
--   App. B, p. 6 (used in (23), p. 3) — composition of pure-loss channels: Eη ∘ Eη′ = Eηη′
-- statement:
--   Let $\mathcal E_\eta$ and $\mathcal E_{\eta'}$ be pure-loss channels with transmissivities $\eta,\eta'\in(0,1)$. For every single-mode density operator $\rho$,
--   $$\mathcal E_\eta\big(\mathcal E_{\eta'}(\rho)\big)=\mathcal E_{\eta\eta'}(\rho),$$
--   entry by entry in the number basis, and every series defining the three channel outputs converges absolutely.
--
--   Two beam splitters in sequence attenuate like a single beam splitter with the product transmissivity. In the paper this is the "combination relation" derived from the Gaussian composition rule (B4) and the parameters (B5), and it is the step that turns $\mathcal E_\eta\circ\mathcal E_{\xi^2}$ into $\mathcal E_{\eta\xi^2}$ in (23).
--
--   **Formalization Note** The channels are the published vacuum-loss kernels on number-basis matrices; $\rho$ satisfies the published density predicate. The paper derives the relation from covariance matrices; here it is stated directly on Fock matrices, for all densities.
-- source:
--   Namiki, Teleportation stretching for single-mode Gaussian channels, arXiv:1603.05292v1, p. 6, App. B after (B5) (Eη∘Eη′ = Eηη′), used on p. 3 before (23)

import Mathlib
import Definitions.Def_NamikiStretch_Lossy_Protocol

namespace NamikiStretch.Lossy

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P39
open QAlgorithms.Papers.Independent.Frontier30.P21

theorem loss_comp (η η' : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hη'0 : 0 < η')
    (hη'1 : η' < 1) (X : FockOperator) (hX : IsDensity X) :
    let K : ℕ → ℕ → ℂ := fun m n => X (fockKet n) m
    (∀ a b : ℕ, Summable (vacuumLossTerm η' K a b)) ∧
    (∀ a b : ℕ, Summable (vacuumLossTerm η (vacuumLossKernel η' K) a b)) ∧
    (∀ a b : ℕ, Summable (vacuumLossTerm (η * η') K a b)) ∧
    ∀ m n : ℕ, vacuumLossKernel η (vacuumLossKernel η' K) m n =
      vacuumLossKernel (η * η') K m n := by sorry
end NamikiStretch.Lossy
