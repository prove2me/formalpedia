-- Prove2me | Theorems.Thm_OAI_CubicTorus_corner_grid_269
-- name    : OAI.CubicTorus.corner_grid_269
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:53:59.071434+00:00
-- url     : https://prove2.me/theorems/f8eca3cd-2ebd-46ab-8ffb-5b5593ebbe88
-- title:
--   OAI.CubicTorus.corner_grid_269: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.corner_grid_269` of [lean/OAI/Geometry/CubicTorus/Profiles/CornerGrid269.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/CornerGrid269.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`):
--
--   ```lean
--   lemma corner_grid_269 {t d x : ℝ} (h : CornerRootData t d x)
--       (hl : (1/2 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
--       (hd : (0/1 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
--       d+(t^2+(t+x*d)^2)/Real.pi<1
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CornerRootData` (definitions bundle `OAIQ079A000` of this split).
--
--   **Used by.** The proofs of `OAI.CubicTorus.fourCorner_normalized_contradiction` and `OAI.CubicTorus.secondCorner_endpoint_contradiction` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/CornerGrid269.lean (declaration OAI.CubicTorus.corner_grid_269)

import Mathlib
import Definitions.Def_OAIQ079A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace CubicTorus

lemma corner_grid_269 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/2 : ℝ)≤t) (hu : t≤(1/1 : ℝ))
    (hd : (0/1 : ℝ)≤d) (he : d≤(13/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  sorry

end CubicTorus
end
end

end OAI
end
