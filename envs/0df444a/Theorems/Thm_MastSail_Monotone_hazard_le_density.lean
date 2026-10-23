-- Prove2me | Theorems.Thm_MastSail_Monotone_hazard_le_density
-- name    : MastSail.Monotone.hazard_le_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:26.134524+00:00
-- url     : https://prove2.me/theorems/7fb636ba-8386-4074-a291-c33218eda2e3
-- title:
--   Proof of Proposition 3, p. oa6 — survival ratio ≤ density ratio of demand, strictly under strict MLRP
-- statement:
--   Assume the standing assumptions of the model ($0<\bar I<\bar Q$, positive continuous densities on the closed supports, MLRP (1)). Then for every $i\in[0,\bar I]$,
--   $$\frac{1-G(i\mid e^L_m)}{1-G(i\mid e^H_m)}\le\frac{g(i\mid e^L_m)}{g(i\mid e^H_m)},$$
--   and if moreover $g(\cdot\mid e^L_m)/g(\cdot\mid e^H_m)$ is strictly decreasing on $[0,\bar Q]$ (strict MLRP of $g$), the inequality is strict for every $i\in[0,\bar I]$.
--
--   This comparison gives $\varphi^{SO}(i)\ge\varphi^{NSO}(i,i)$ for every inventory level, which is the key step in showing that the mast never starts above the sail.
--
--   **Formalization Note** The paper states the strict inequality and attributes it to increasing failure rates. Under the paper's weak MLRP only $\le$ holds (equality when the demand ratio is constant on $[i,\bar Q]$), so the strict form is stated under strict MLRP of $g$.
-- source:
--   Dai, Ke & Ryan, SSRN 3235866, p. oa6, proof of Proposition 3

import Mathlib
import Definitions.Def_MastSail_Monotone_Model

namespace MastSail.Monotone
theorem hazard_le_density (M : Model) (hM : M.Standing) :
    (∀ i ∈ Set.Icc 0 M.Ibar, (1 - cdf M.gL i) / (1 - cdf M.gH i) ≤ M.gL i / M.gH i) ∧
    (M.StrictMLRPg →
      ∀ i ∈ Set.Icc 0 M.Ibar, (1 - cdf M.gL i) / (1 - cdf M.gH i) < M.gL i / M.gH i) := by sorry
end MastSail.Monotone
