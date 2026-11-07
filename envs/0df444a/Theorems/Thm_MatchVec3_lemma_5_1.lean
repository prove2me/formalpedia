-- Prove2me | Theorems.Thm_MatchVec3_lemma_5_1
-- name    : MatchVec3.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:59.05156+00:00
-- url     : https://prove2.me/theorems/0a09ba08-af40-4624-bd46-ee8360ba5a4a
-- title:
--   Lemma 5.1: base fiber bound $M_q(U)\le bn+1$
-- statement:
--   Assume the two-residue structure on $m=p^aq^b$, and let $(U,V)$ be a matching vector family in $\mathbb Z^n_m$ with off-diagonal residues in $\{\alpha,\beta\}$. Then
--
--   $$M_q(U)\le bn+1.$$
--
--   It is the base case of the induction on the sum length $L$.
--
--   Differences from the source:
--   - generalization: "minimal non-prime-power divisor" and "3-restricted" as hypotheses → ResidueStructure and OffDiagIn, with no minimality; reason: these are all the proof uses, Lemma 2.3 yields them from the page's hypotheses, and they imply 3-restriction; if only one of α, β occurs the statement still holds
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), Lemma 5.1, p.13

import Mathlib
import Definitions.Def_MatchVec3_IsMVFamily
import Definitions.Def_MatchVec3_ResidueStructure
import Definitions.Def_MatchVec3_OffDiagIn
import Definitions.Def_MatchVec3_fiberMax

namespace MatchVec3

/-- **Lemma 5.1 (Base fiber bound)** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256
44199413…), Lemma 5.1, p.13): with the notation of §5, `M_q(U) ≤ bn + 1`.

**Formalization Note** "With notation as above" is §5's preamble: `ResidueStructure` and off-diagonal
values in `{α, β}`. The minimality of the modulus is not assumed, since those are the consequences of
it (Lemma 2.3) that the proof uses. Every `n`, including `n = 0`, is covered. -/
theorem lemma_5_1 {m p q a b n K : ℕ} {α β : ZMod m}
    (hstr : ResidueStructure m p q a b α β)
    (U V : Fin K → Fin n → ZMod m) (hfam : IsMVFamily U V) (hoff : OffDiagIn U V α β) :
    fiberMax U q ≤ b * n + 1 := by sorry

end MatchVec3
