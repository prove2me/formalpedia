-- Prove2me | Theorems.Thm_FriedmannEquations_cosmological_constant_as_vacuum_energy
-- name    : FriedmannEquations.cosmological_constant_as_vacuum_energy
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T22:27:37.695494+00:00
-- url     : https://prove2.me/theorems/2690df86-87cf-4861-ab8e-3d49bd427d71
-- title:
--   The cosmological constant is absorbed by $\rho\to\rho-\Lambda/\kappa$, $p\to p+\Lambda/\kappa$
-- statement:
--   Let $G>0$ and put $\kappa = 8\pi G$ (units $c=1$). For any $\Lambda,k$, scale factor $R$, density $\rho$, pressure $p$ and time $t$:
--
--   * the first Friedmann equation with cosmological constant $\Lambda$ and density $\rho - \Lambda/\kappa$ holds at $t$ iff the first Friedmann equation with $\Lambda = 0$ and density $\rho$ holds at $t$;
--   * the second Friedmann equation with cosmological constant $\Lambda$, density $\rho - \Lambda/\kappa$ and pressure $p + \Lambda/\kappa$ holds at $t$ iff the second Friedmann equation with $\Lambda = 0$, density $\rho$ and pressure $p$ holds at $t$.
--
--   So the $\Lambda$-term is the same as a fluid component with density $\Lambda/\kappa$ and pressure $-\Lambda/\kappa$ (equation of state $p = -\rho$).
-- source:
--   Wikipedia, "Friedmann equations", revision oldid=1374073387, https://en.wikipedia.org/w/index.php?title=Friedmann_equations&oldid=1374073387 (the PDF supplied with this proposal), section "Cosmological constant", pp. 6–7.

import Definitions.Def_FriedmannEquations_Defs
import Mathlib

open FriedmannEquations

theorem FriedmannEquations.cosmological_constant_as_vacuum_energy
    (G Λ k : ℝ) (hG : 0 < G) (R ρ p : ℝ → ℝ) (t : ℝ) :
    (FirstFriedmannEq G Λ k R (fun s => ρ s - Λ / (8 * Real.pi * G)) t ↔
      FirstFriedmannEq G 0 k R ρ t) ∧
    (SecondFriedmannEq G Λ R (fun s => ρ s - Λ / (8 * Real.pi * G))
        (fun s => p s + Λ / (8 * Real.pi * G)) t ↔
      SecondFriedmannEq G 0 R ρ p t) := by sorry
