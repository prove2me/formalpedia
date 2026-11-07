-- Prove2me | Theorems.Thm_MatchVec3_matching_number_bound
-- name    : MatchVec3.matching_number_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:41:42.874928+00:00
-- url     : https://prove2.me/theorems/bdeaf885-dd94-43e9-a1dd-1a049556132a
-- title:
--   Proof of Theorem 5.2: $\nu(F)\le n^{O_m(L)}$
-- statement:
--   There is a constant $C$ depending only on $m$ such that the following holds. Assume the two-residue structure on $m=p^aq^b$, let $n\ge1$, and let $(U,V)$ be a matching vector family in $\mathbb Z^n_m$ with off-diagonal residues in $\{\alpha,\beta\}$. Then for every $L\ge1$ and every $L$-sum fiber $F$ of $U$,
--
--   $$\nu(F)\le n^{CL}.$$
--
--   This is the main new step of the paper: a matching in a fiber yields an identity matrix of low rank.
--
--   Differences from the source:
--   - encoding: ν(F) ≤ n^{O_m(L)} with no restriction on n → n ≥ 1; reason: n = 0 is the zero-dimensional space, where 0^{CL} = 0 is not what the page's notation means; at n = 1 the Lean says ν(F) ≤ 1, which holds (the p-adic valuations of the u_i order the β-relation, and the pivot of least valuation contradicts the β-count separation)
--   - generalization: L > q → every L ≥ 1; reason: the argument for this step does not use L > q
--   - generalization: "minimal non-prime-power divisor" and "3-restricted" as hypotheses → ResidueStructure and OffDiagIn, with no minimality; reason: these are all the proof uses, Lemma 2.3 yields them from the page's hypotheses, and they imply 3-restriction; if only one of α, β occurs the statement still holds
--   - encoding: n^{O_m(L)} → ∃ C after m, p, q, a, b and before n, the family, α, β, L; reason: the meaning of O_m(·): m determines p, q, a, b
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), proof of Theorem 5.2, p.16

import Mathlib
import Definitions.Def_MatchVec3_IsMVFamily
import Definitions.Def_MatchVec3_ResidueStructure
import Definitions.Def_MatchVec3_OffDiagIn
import Definitions.Def_MatchVec3_fiber
import Definitions.Def_MatchVec3_matchingNumber

namespace MatchVec3

/-- **The matching-number bound** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256
44199413…), proof of Theorem 5.2, p.16): `ν(F) ≤ n^(O_m(L))` for an `L`-sum fiber `F`.

**Formalization Note** `C` comes after `m, p, q, a, b` and before `n`, the family, `α`, `β`, `L`, `x`.
The statement is for every `n ≥ 1` (at `n = 1` it says `ν(F) ≤ 1`, which holds: the `p`-adic valuations
of the `u_i` order the `β`-relation, and the pivot of least valuation contradicts the `β`-count
separation) and for every `L ≥ 1`, since the page's argument for this step does not use `L > q`. -/
theorem matching_number_bound (m p q a b : ℕ) : ∃ C : ℕ, ∀ (n K : ℕ), 1 ≤ n →
    ∀ (α β : ZMod m) (U V : Fin K → Fin n → ZMod m),
    ResidueStructure m p q a b α β → IsMVFamily U V → OffDiagIn U V α β →
    ∀ (L : ℕ) (x : Fin n → ZMod m), 1 ≤ L →
      matchingNumber (fiber U L x) ≤ n ^ (C * L) := by sorry

end MatchVec3
