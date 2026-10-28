-- Prove2me | Theorems.Thm_OAI_CubicTorus_secondCorner_endpoint_contradiction
-- name    : OAI.CubicTorus.secondCorner_endpoint_contradiction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:38:01.606663+00:00
-- url     : https://prove2.me/theorems/032ead66-eac6-47fa-b2c8-c788a8a640e7
-- title:
--   OAI.CubicTorus.secondCorner_endpoint_contradiction: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.secondCorner_endpoint_contradiction` of [lean/OAI/Geometry/CubicTorus/Main.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Main.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open Set`):
--
--   ```lean
--   theorem secondCorner_endpoint_contradiction {A h b r s : ℝ}
--       (hA0 : 0<A) (hA : A≤1) (hh : 0≤h)
--       (hb0 : 0≤b) (hb1 : b<1) (hr0 : 0 ≤ r) (hr1 : r≤1/Real.pi)
--       (hs1 : s≤1)
--       (htop : Real.sqrt (Real.pi*r)≤A*b-h*(1/Real.pi-r))
--       (hbottom : Real.sqrt (Real.pi*(1-s))≤A*b+h*(s-1/Real.pi))
--       (hdrop : s-r≤A*Real.sqrt (1-b))
--       (hbmax : 2/3≤b) (hxcap : h*A≤7/4) : False
--   ```
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_cylinder_interval_standard`, `OAI_CubicTorus_isMinimizerAt_second_transition_standard`, `OAI.CubicTorus.isMinimizerAt_small_slab_standard`, `OAI.CubicTorus.isoperimetricProfile_cylinder_interval` and `OAI.CubicTorus.isoperimetricProfile_second_transition` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Main.lean (declaration OAI.CubicTorus.secondCorner_endpoint_contradiction)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
namespace CubicTorus

theorem secondCorner_endpoint_contradiction {A h b r s : ℝ}
    (hA0 : 0<A) (hA : A≤1) (hh : 0≤h)
    (hb0 : 0≤b) (hb1 : b<1) (hr0 : 0 ≤ r) (hr1 : r≤1/Real.pi)
    (hs1 : s≤1)
    (htop : Real.sqrt (Real.pi*r)≤A*b-h*(1/Real.pi-r))
    (hbottom : Real.sqrt (Real.pi*(1-s))≤A*b+h*(s-1/Real.pi))
    (hdrop : s-r≤A*Real.sqrt (1-b))
    (hbmax : 2/3≤b) (hxcap : h*A≤7/4) : False := by
  sorry

end CubicTorus

end
end

end OAI
end
