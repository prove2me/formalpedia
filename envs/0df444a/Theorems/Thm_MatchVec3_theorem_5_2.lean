-- Prove2me | Theorems.Thm_MatchVec3_theorem_5_2
-- name    : MatchVec3.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:58.395203+00:00
-- url     : https://prove2.me/theorems/ed6d8e23-51e2-4076-977f-c9ead10c6bda
-- title:
--   Theorem 5.2: long-sum fiber bound
-- statement:
--   There is a constant $C>0$ depending only on $m$ such that the following holds. Assume the two-residue structure on $m=p^aq^b$ with $p<q$, let $n\ge1$, and let $(U,V)$ be a matching vector family in $\mathbb Z^n_m$ with off-diagonal residues in $\{\alpha,\beta\}$. Then for all $L\ge q$,
--
--   $$M_L(U)\le\exp\big(C(L^2\log n+L\log L)\big).$$
--
--   This bound keeps fibers small for sums of length up to order $\sqrt{n/\log n}$, which is what drives the main theorem.
--
--   Differences from the source:
--   - generalization: "minimal non-prime-power divisor" and "3-restricted" as hypotheses → ResidueStructure and OffDiagIn, with no minimality; reason: these are all the proof uses, Lemma 2.3 yields them from the page's hypotheses, and they imply 3-restriction; if only one of α, β occurs the statement still holds
--   - encoding: exp(O_m(L² log n + L log L)) → ∃ C after m, p, q, a, b and before n, the family, α, β, L; reason: the meaning of O_m(·): m determines p, q, a, b
--   - encoding: n unrestricted → n ≥ 1; reason: log n is undefined on the page at n = 0; at n = 1 the bound rests on L log L, with L ≥ q ≥ 3
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), Theorem 5.2, p.14

import Mathlib
import Definitions.Def_MatchVec3_IsMVFamily
import Definitions.Def_MatchVec3_ResidueStructure
import Definitions.Def_MatchVec3_OffDiagIn
import Definitions.Def_MatchVec3_fiberMax

namespace MatchVec3

/-- **Theorem 5.2 (Long-sum fiber bound)** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256
44199413…), Theorem 5.2, p.14): for a 3-restricted matching vector family modulo `m = p^a q^b`, `p < q`,
as in Lemma 2.3, for all `L ≥ q`: `M_L(U) ≤ exp(O_m(L² log n + L log L))`.

**Formalization Note** `C` comes after `m, p, q, a, b` and before `n`, the family, `α`, `β`, `L`. The
hypotheses are the consequences of minimality that the proof uses (`ResidueStructure`, off-diagonal
values in `{α, β}`), and they imply 3-restriction. `1 ≤ n` is needed for `log n` on the page; at `n = 1`
the bound rests on `L log L`. -/
theorem theorem_5_2 (m p q a b : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (n K : ℕ), 1 ≤ n →
    ∀ (α β : ZMod m) (U V : Fin K → Fin n → ZMod m),
    ResidueStructure m p q a b α β → IsMVFamily U V → OffDiagIn U V α β →
    ∀ L : ℕ, q ≤ L →
      (fiberMax U L : ℝ) ≤ Real.exp (C * (L ^ 2 * Real.log n + L * Real.log L)) := by sorry

end MatchVec3
