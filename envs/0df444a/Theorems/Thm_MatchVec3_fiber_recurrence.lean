-- Prove2me | Theorems.Thm_MatchVec3_fiber_recurrence
-- name    : MatchVec3.fiber_recurrence
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:07.438726+00:00
-- url     : https://prove2.me/theorems/c8f641b7-5c5f-43e9-93d9-e8a10a8aa6c9
-- title:
--   Proof of Theorem 5.2: $M_L(U)\le L\,n^{O_m(L)}M_{L-1}(U)$
-- statement:
--   There is a constant $C$ depending only on $m$ such that the following holds. Assume the two-residue structure on $m=p^aq^b$, and let $(U,V)$ be a matching vector family in $\mathbb Z^n_m$ with off-diagonal residues in $\{\alpha,\beta\}$. Then for every $L>q$,
--
--   $$M_L(U)\le L\,n^{CL}\,M_{L-1}(U).$$
--
--   Iterating this recurrence from the base case $M_q(U)\le bn+1$ gives the long-sum fiber bound.
--
--   Differences from the source:
--   - generalization: "minimal non-prime-power divisor" and "3-restricted" as hypotheses → ResidueStructure and OffDiagIn, with no minimality; reason: these are all the proof uses, Lemma 2.3 yields them from the page's hypotheses, and they imply 3-restriction; if only one of α, β occurs the statement still holds
--   - encoding: n^{O_m(L)} → ∃ C after m, p, q, a, b and before n, the family, α, β, L; reason: the meaning of O_m(·): m determines p, q, a, b
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), proof of Theorem 5.2, p.16

import Mathlib
import Definitions.Def_MatchVec3_IsMVFamily
import Definitions.Def_MatchVec3_ResidueStructure
import Definitions.Def_MatchVec3_OffDiagIn
import Definitions.Def_MatchVec3_fiberMax

namespace MatchVec3

/-- **The fiber recurrence** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256 44199413…),
proof of Theorem 5.2, p.16): `M_L(U) ≤ L n^(O_m(L)) M_{L-1}(U)` for `L > q`.

**Formalization Note** `C` comes after `m, p, q, a, b` and before `n`, the family, `α`, `β`, `L`. The
statement is for every `n`; at `n = 0` the family has at most one member, so both sides vanish. -/
theorem fiber_recurrence (m p q a b : ℕ) : ∃ C : ℕ, ∀ (n K : ℕ),
    ∀ (α β : ZMod m) (U V : Fin K → Fin n → ZMod m),
    ResidueStructure m p q a b α β → IsMVFamily U V → OffDiagIn U V α β →
    ∀ L : ℕ, q < L →
      fiberMax U L ≤ L * n ^ (C * L) * fiberMax U (L - 1) := by sorry

end MatchVec3
