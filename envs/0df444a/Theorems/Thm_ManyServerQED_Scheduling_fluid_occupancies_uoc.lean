-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_fluid_occupancies_uoc
-- name    : ManyServerQED.Scheduling.fluid_occupancies_uoc
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T20:16:57.033867+00:00
-- url     : https://prove2.me/theorems/8c7033cb-32bf-59d7-b336-51269492eead
-- title:
--   Fluid service and waiting occupancies under work conservation
-- statement:
--   For a sequence of controlled, work-conserving many-server systems with convergent diffusion-scaled initial populations, write \(\bar\Psi^n=\Psi^n/n\) for the service occupancies and \(\bar\Phi^n=(X^n-\Psi^n)/n\) for the waiting occupancies. Then \((\bar\Psi^n,\bar\Phi^n)\to(\rho,0)\) uniformly on compact time intervals in probability. Here \(\rho_i=\lambda_i/\mu_i\).
-- source:
--   Atar, Mandelbaum and Reiman, Scheduling a multi class queue with many exponential servers, Lemma 4(ii), https://arxiv.org/abs/math/0407058

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory Filter Topology ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy
open scoped ENNReal

theorem ManyServerQED.Scheduling.fluid_occupancies_uoc {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n)) :
    UocInProb M.P (fun n ω t => Psibar n (Ψ n) ω t) (fun _ => M.rho) ∧
      UocInProb M.P (fun n ω t => Phibar n (X n) (Ψ n) ω t)
        (fun _ => 0) := by sorry
