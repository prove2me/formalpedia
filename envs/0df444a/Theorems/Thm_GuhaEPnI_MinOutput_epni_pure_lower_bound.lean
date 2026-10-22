-- Prove2me | Theorems.Thm_GuhaEPnI_MinOutput_epni_pure_lower_bound
-- name    : GuhaEPnI.MinOutput.epni_pure_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:56.550014+00:00
-- url     : https://prove2.me/theorems/38e38df2-5e25-4f53-b17f-bcd48c6cda40
-- title:
--   Eqs. (16)–(17), p. 3 — EPnI lower bound for pure first input
-- statement:
--   Let $n\ge1$, $\eta\in[0,1]$, and $K\ge0$. Suppose the first beam-splitter input $\rho_a$ is pure and has finite energy, and the second input $\rho_b$ has finite energy and entropy $S(\rho_b)=n g(K)$. For any corresponding output $\rho_c$, its entropy photon-number obeys
--
--   $$g^{-1}\!\left(\frac{S(\rho_c)}{n}\right)\ge(1-\eta)K.$$
--
--   This is the common inequality in Eqs. (16) and (17).
--
--   **Formalization Note** Finite energy is required by the referenced EPnI and makes the real-valued entropy meaningful; $n\ge1$ makes division by $n$ valid.
-- source:
--   Guha, Erkmen & Shapiro, The Entropy Photon-Number Inequality and its Consequences, arXiv:0710.5666v2, p. 3, Eqs. (16)–(17)

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_GuhaEPnI_MinOutput_States

namespace GuhaEPnI.MinOutput
open OAI.EntropyPhotonNumber

theorem epni_pure_lower_bound (n : ℕ) (hn : 1 ≤ n) (η : ℝ)
    (hη : η ∈ Set.Icc 0 1) (K : ℝ) (hK : 0 ≤ K)
    (ρA ρB ρC : State n) (hA : IsPure ρA)
    (hEA : FiniteEnergy ρA) (hEB : FiniteEnergy ρB)
    (hB : entropy ρB = (n : ℝ) * g K)
    (hC : IsBeamSplitterOutput η ρA ρB ρC) :
    (1 - η) * K ≤ gInv (entropy ρC / n) := by sorry

end GuhaEPnI.MinOutput
