-- Prove2me | Theorems.Thm_LiouvilleDiffAlg_ratFunc_standardDerivation_existsUnique
-- name    : LiouvilleDiffAlg.ratFunc_standardDerivation_existsUnique
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T17:29:16.029008+00:00
-- url     : https://prove2.me/theorems/c1ae3ec2-d54f-4383-94e4-cdab560a8d25
-- title:
--   $\mathbb{C}(x)$ has a unique standard derivation $d/dx$
-- statement:
--   There is exactly one derivation $D$ on the field $\mathbb{C}(x)$ of complex rational functions such that
--   $$D(p) = p' \qquad \text{for all } p \in \mathbb{C}[x],$$
--   where $p'$ is the formal derivative of the polynomial $p$.
--
--   This makes $\mathbb{C}(x)$ with $d/dx$ a well-defined differential field, the setting of all examples in the mission. It also shows that the examples, which assume a standard derivation, are not vacuous.
-- source:
--   Wikipedia, "Liouville's theorem (differential algebra)", revision oldid=1349223559, https://en.wikipedia.org/w/index.php?title=Liouville%27s_theorem_(differential_algebra)&oldid=1349223559, section "Examples": "the field $\mathbb{C}(x)$ of rational functions in a single variable has a derivation given by the standard derivative with respect to that variable"

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_RatFunc

open scoped Differential

namespace LiouvilleDiffAlg

theorem ratFunc_standardDerivation_existsUnique :
    ∃! d : Differential (RatFunc ℂ), @IsStandardDerivation d := by sorry

end LiouvilleDiffAlg
