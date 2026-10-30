-- Prove2me | Theorems.Thm_FreedmanTail_lemma_3_1_g_strictMono
-- name    : FreedmanTail.lemma_3_1_g_strictMono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:09:10.471637+00:00
-- url     : https://prove2.me/theorems/34b5de73-02bb-414c-afac-afb04643d9ed
-- title:
--   (3.1) Lemma: $g(x) = (e^x - 1 - x)/x^2$ is increasing
-- statement:
--   Let $g(0) = \tfrac12$ and $g(x) = (e^x - 1 - x)/x^2$ for $x \ne 0$. Then $g$ is strictly increasing on $\mathbb R$:
--   $$x < y \implies g(x) < g(y).$$
--   The monotonicity of $g$ gives the exponential moment bound (3.2) by comparing $g(\lambda x)$ with $g(\lambda)$.
--
--   Differences from the source:
--   - reading: g is increasing → StrictMono gFun (strictly increasing); reason: the paper's proof shows g′(x) > 0 for x ≠ 0; strictly increasing implies nondecreasing, so this is the stronger reading
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975) 100–118, doi:10.1214/aop/1176996452, (3.1) Lemma, p. 106

import Mathlib
import Definitions.Def_FreedmanTail_gFun

namespace FreedmanTail

/-- **(3.1) Lemma: `g` is increasing.**
Freedman, *On Tail Probabilities for Martingales*, Ann. Probab. 3 (1975) 100–118,
(3.1) Lemma, p. 106: "Let g(0) = ½ and g(x) = (e^x − 1 − x)/x² for x ≠ 0. Then g is
increasing."

**Formalization Note.** "Increasing" is read as strictly increasing (`StrictMono`): the paper's
proof shows `g′(x) > 0` for `x ≠ 0`, and `StrictMono` implies `Monotone`, so this is the
stronger of the two readings. -/
theorem lemma_3_1_g_strictMono : StrictMono gFun := by sorry

end FreedmanTail
