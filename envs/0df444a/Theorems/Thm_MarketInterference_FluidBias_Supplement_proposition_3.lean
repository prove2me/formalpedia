-- Prove2me | Theorems.Thm_MarketInterference_FluidBias_Supplement_proposition_3
-- name    : MarketInterference.FluidBias.Supplement.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:46:00.350104+00:00
-- url     : https://prove2.me/theorems/96a2d1ff-dbfc-468a-80cc-60d02520ee10
-- title:
--   Proposition 3 (supports Theorem 3) — the rescaled-count Two-LP formula
-- statement:
--   Let $N$ be any finite capacitated matching network, $\tau>0$ and $0<\rho<1$. For every observed nonnegative integer control, treatment and supply vector $C,T,S$, the plug-in Two-LP estimator of Definition 4 satisfies
--   $$
--   \widehat\Delta^\tau_{2LP}=\frac1\tau\left[\Phi_\tau(T/\rho,S)-\Phi_\tau(C/(1-\rho),S)\right].
--   $$
--   This identity connects the maximum-likelihood plug-in estimator to the scaled count-level optimization problems used in the fluid-limit analysis.
--
--   **Formalization Note** The divisions use positive $\tau$, $\rho$ and $1-\rho$. The network has arbitrary finite intermediate nodes and arcs, arbitrary real arc values and nonnegative capacities. The formula is deterministic and requires no arrival-law or uniqueness premise.
--
--   Differences from the source:
--   - encoding: finite source types and path sums → zero-based Fin types, finite arc types and finite-support path flows; reason: the same finite network and all of its supply-to-demand paths, including intermediate nodes
--   - generalization: the surrounding standing Assumptions 1–3 → the rescaling identity for every observed count vector, without blindness, uniqueness or sign consistency; reason: the proof on p. 43 uses only the MLE formulas and Lemma 1; the source experiment is a special case
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 17, Proposition 3; p. 43, proof

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_Supplement_TwoLP

namespace MarketInterference.FluidBias.Supplement

theorem proposition_3 {nd ns : ℕ} {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
    (N : Network nd ns I E) (ρ τ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 < τ)
    (z : Counts nd ns) :
    twoLP N ρ τ z = (1 / τ) *
      (Phi N τ (fun i => (1 / ρ) * (z.1.2 i : ℝ)) (fun j => (z.2 j : ℝ)) -
       Phi N τ (fun i => (1 / (1 - ρ)) * (z.1.1 i : ℝ)) (fun j => (z.2 j : ℝ))) := by sorry

end MarketInterference.FluidBias.Supplement
