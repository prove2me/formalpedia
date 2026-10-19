-- Prove2me | Theorems.Thm_OAI_C0Absorption_tailFactor_lipschitz
-- name    : OAI.C0Absorption.tailFactor_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:03:30.553312+00:00
-- url     : https://prove2.me/theorems/7f5afe71-32cb-4bad-886a-452501791186
-- title:
--   Tail factors are Lipschitz
-- statement:
--   $c_0$ is the Banach space of real sequences tending to zero with the sup norm, $B$ is its closed unit ball, and for a finite set $I$ of coordinates the cube $[-1,1]^I$ is the image of $B$ under restriction to $I$. For $s\in c_0$ let $\tau_N(s)=\sup_{i>N}|s_i|$. For $c>0$ the tail factor
--   $$
--   \mathrm{tailFactor}(c,N,s)=\min\bigl(1,\max(2-\tau_N(s)/c,0)\bigr)
--   $$
--   is $c^{-1}$-Lipschitz in $s$.
--
--   Tail factors switch from $1$ to $0$ as the tail grows from $c$ to $2c$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Coordinates.lean#L315-L332

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem OAI.C0Absorption.tailFactor_lipschitz {c : ℝ} (hc : 0 < c) (N : ℕ) :
    LipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ (tailFactor c N) := by sorry
