-- Prove2me | Theorems.Thm_OAI_FiniteAssociation_increasing
-- name    : OAI.FiniteAssociation.increasing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:45:41.668298+00:00
-- url     : https://prove2.me/theorems/5d8ea5ae-c2e2-40fe-a55a-03b71a152796
-- title:
--   Harris inequality for increasing functions of finitely many bits
-- statement:
--   For a finite index set $E$ and parameters $p_e\in[0,1]$, $\mathbb P_p$ is the product law of independent bits with $\mathbb P(\omega_e=1)=p_e$, and $\mathbb E_p$ its expectation; configurations are ordered coordinatewise. If $f,g$ are increasing real functions of the configuration, then they are positively correlated:
--   $$
--   \mathbb E_p[f]\,\mathbb E_p[g]\le\mathbb E_p[fg].
--   $$
--
--   This is the Harris–FKG inequality for product measures.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/ProductCylinder.lean#L150-L193

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder

open OAI OAI.FiniteAssociation
universe uE uF uI
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
universe u
variable {E : Type u}

theorem OAI.FiniteAssociation.increasing [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (f g : (E → Bool) → ℝ) (hf : Monotone f) (hg : Monotone g) :
    mean p f * mean p g ≤ mean p (fun ω => f ω * g ω) := by sorry
