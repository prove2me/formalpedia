-- Prove2me | Theorems.Thm_HadwigerConj_wagner_colorable_two_pow
-- name    : HadwigerConj.wagner_colorable_two_pow
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T23:34:29.312664+00:00
-- url     : https://prove2.me/theorems/16f7395b-eb6d-458f-8c4f-6dd868f50281
-- title:
--   Wagner 1964: no $K_{t+1}$ minor $\Rightarrow$ $2^t$-colourable
-- statement:
--   For every integer $t\ge 0$, every finite graph $G$ with no $K_{t+1}$ minor is $2^t$-colourable:
--
--   $$K_{t+1}\not\preceq G\ \Longrightarrow\ \chi(G)\le 2^{t}.$$
--
--   This is the first general bound on the chromatic number of graphs excluding a complete minor.
-- source:
--   P. Seymour, "Hadwiger's conjecture" (survey), in: Open Problems in Mathematics, Springer, 2016 (uploaded PDF `paper.pdf`), Section 3, first paragraph (p. 4: “As Wagner proved in 1964, all graphs with no K_{t+1} minor are 2^t-colourable”)

import Mathlib
import Definitions.Def_HadwigerConj_Defs

namespace HadwigerConj
theorem wagner_colorable_two_pow (t : ℕ) {V : Type} [Finite V] (G : SimpleGraph V)
    (hG : ¬ HasCompleteMinor G (t + 1)) : G.Colorable (2 ^ t) := by sorry
end HadwigerConj
