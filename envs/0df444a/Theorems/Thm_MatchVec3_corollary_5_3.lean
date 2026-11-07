-- Prove2me | Theorems.Thm_MatchVec3_corollary_5_3
-- name    : MatchVec3.corollary_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:04.622494+00:00
-- url     : https://prove2.me/theorems/b81d9973-fba9-4018-bb68-45fde8ada006
-- title:
--   Corollary 5.3: entropy growth
-- statement:
--   There is a constant $C>0$ depending only on $m$ such that the following holds. Assume the two-residue structure on $m=p^aq^b$, let $n\ge1$, and let $(U,V)$ be a matching vector family of size $K$ in $\mathbb Z^n_m$ with off-diagonal residues in $\{\alpha,\beta\}$. Then for all $q\le L\le K$,
--
--   $$H_\infty(S_L^*(U))\ge L\log K-C(L^2\log n+L\log L).$$
--
--   Compared with the support bound $H_\infty(S_L^*(U))\le n\log m$, this gives the final estimate on $K$.
--
--   Differences from the source:
--   - generalization: "minimal non-prime-power divisor" and "3-restricted" as hypotheses → ResidueStructure and OffDiagIn, with no minimality; reason: these are all the proof uses, Lemma 2.3 yields them from the page's hypotheses, and they imply 3-restriction; if only one of α, β occurs the statement still holds
--   - encoding: O_m(L² log n + L log L) → ∃ C after m, p, q, a, b and before n, the family, α, β, L; reason: the meaning of O_m(·): m determines p, q, a, b
--   - encoding: n unrestricted → n ≥ 1; reason: as in Theorem 5.2
--   - encoding: all L ≥ q → q ≤ L ≤ K; reason: S*_L(U) is defined only for L ≤ K (§6, p.17)
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), Corollary 5.3, p.16

import Mathlib
import Definitions.Def_MatchVec3_IsMVFamily
import Definitions.Def_MatchVec3_ResidueStructure
import Definitions.Def_MatchVec3_OffDiagIn
import Definitions.Def_MatchVec3_sumDist
import Definitions.Def_MatchVec3_minEntropy

namespace MatchVec3

/-- **Corollary 5.3 (Entropy growth)** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256
44199413…), Corollary 5.3, p.16): for all `L ≥ q`,
`H∞(S*_L(U)) ≥ L log K − O_m(L² log n + L log L)`.

**Formalization Note** `C` is placed as in `theorem_5_2`. `L ≤ K` is the page's condition for `S*_L(U)`
to be well defined (§6, p.17), and it gives `K ≥ q ≥ 3`, so `log K > 0`. -/
theorem corollary_5_3 (m p q a b : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (n K : ℕ), 1 ≤ n →
    ∀ (α β : ZMod m) (U V : Fin K → Fin n → ZMod m),
    ResidueStructure m p q a b α β → IsMVFamily U V → OffDiagIn U V α β →
    ∀ (L : ℕ) (hL : L ≤ K), q ≤ L →
      L * Real.log K - C * (L ^ 2 * Real.log n + L * Real.log L) ≤ minEntropy (sumDist U L hL) := by sorry

end MatchVec3
