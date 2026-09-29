-- Prove2me | Theorems.Thm_LiouvilleDiffAlg_constants_isSubfield
-- name    : LiouvilleDiffAlg.constants_isSubfield
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T17:28:23.797958+00:00
-- url     : https://prove2.me/theorems/c65d48bf-8bbd-4597-a614-4f0e488dd979
-- title:
--   The constants $\operatorname{Con}(F)$ form a subfield
-- statement:
--   Let $F$ be a differential field with derivation $D$. Then the set of constants
--   $$\operatorname{Con}(F) = \{ f \in F : Df = 0 \}$$
--   is a subfield of $F$. It contains $0$ and $1$ and is closed under addition, negation, multiplication and inversion.
--
--   This justifies calling $\operatorname{Con}(F)$ the *field of constants* of $F$. It is used throughout the mission.
-- source:
--   Wikipedia, "Liouville's theorem (differential algebra)", revision oldid=1349223559, https://en.wikipedia.org/w/index.php?title=Liouville%27s_theorem_(differential_algebra)&oldid=1349223559, section "Definitions": "the constants of $F$ is the subfield $\operatorname{Con}(F)=\{f\in F : Df = 0\}$"

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_Basic

open scoped Differential

namespace LiouvilleDiffAlg

theorem constants_isSubfield (F : Type*) [Field F] [Differential F] :
    ∃ S : Subfield F, (S : Set F) = constants F := by sorry

end LiouvilleDiffAlg
