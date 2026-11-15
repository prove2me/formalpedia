-- Prove2me | Theorems.Thm_LargeSupplyFPA_Asymptotic_theorem_3_nonnegative_values
-- name    : LargeSupplyFPA.Asymptotic.theorem_3_nonnegative_values
-- status  : Proved
-- author  : @jasonhartline
-- created : 2026-11-14T15:36:55.26189+00:00
-- url     : https://prove2.me/theorems/4106e4b9-dddd-464d-b8d2-7f4ca189311f
-- title:
--   Theorem 3 — atomless approximation for nonnegative values
-- statement:
--   In a multi-unit first-price auction with nonnegative values, every $\varepsilon$-approximate Bayes–Nash equilibrium can be transformed, for every $\omega>0$, into an atomless $(\varepsilon+\omega)$-approximate Bayes–Nash equilibrium with the same expected welfare. An almost-sure upper bound $t$ on any conditional bid distribution becomes the upper bound $t+\omega$.
-- source:
--   Hartline, Shah, and vonAllmen, Robust Analysis of First-Price Auctions with Large Supply, Theorem 3 and its proof, pp. 29–33. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1201.pdf. This version makes nonnegativity of supported values explicit and states the bound on bid increases used in Theorem 2.

import Definitions.Def_LargeSupplyFPA_Asymptotic_Model
import Definitions.Def_LargeSupplyFPA_Asymptotic_Assumptions

open MeasureTheory ProbabilityTheory Set

namespace LargeSupplyFPA.Asymptotic

theorem theorem_3_nonnegative_values {n : ℕ} (k : ℕ) (V : Fin n → Measure ℝ) (E : Fin n → Kernel ℝ ℝ) (ε : ℝ)
    (hV : IsValueProfile V) (hE : IsStrategyProfile E) (hBNE : IsApproxBNE k V E ε)
    (hValue : ∀ i, ∀ v ∈ (V i).support, 0 ≤ v) (ω : ℝ) (hω : 0 < ω) :
    ∃ Et : Fin n → Kernel ℝ ℝ, IsStrategyProfile Et ∧
      IsApproxBNE k V Et (ε + ω) ∧
      IsAtomless V Et ∧ welfare k V E = welfare k V Et ∧
      (∀ i v t, E i v (Iic t) = 1 → Et i v (Iic (t + ω)) = 1) := by sorry

end LargeSupplyFPA.Asymptotic
