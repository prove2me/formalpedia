-- Prove2me | Theorems.Thm_HypRecov_lemma_3_2
-- name    : HypRecov.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:36:49.051727+00:00
-- url     : https://prove2.me/theorems/1a22fde4-c031-4f94-a9e7-4973d84ca4e4
-- title:
--   Lemma 3.2 — boundary sign bound
-- statement:
--   Let $V=S\,\dot\cup\,T$ and call a set crossing if it meets both parts. Let $2\le q\le r$ and let $B_{S,q}$ be the submatrix of the inclusion matrix $W_{q,r}$ with crossing rows ($q$-sets) and crossing columns ($r$-sets). Every nonzero real vector $h$ on the crossing $r$-sets with $B_{S,q}h=0$ satisfies
--   $$|\{e:h_e>0\}|\ge 2^{q-1},\qquad |\{e:h_e<0\}|\ge 2^{q-1}.$$
--
--   Applied to the difference of the boundaries of two hypergraphs with the same $q$-projection, it shows that a cut with fewer than $2^{q-1}$ crossing edges has the same boundary in both; it underlies the capped-cut verifier of Lemma E.1.
--
--   Differences from the source:
--   - encoding: V = S ∪̇ T, h indexed by crossing r-sets → V = Fin n, T = V ∖ S, h on the subtype of crossing r-sets; reason: Lean convention
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Lemma 3.2, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_HypRecov_inclusionMatrix

namespace HypRecov

/-- **Lemma 3.2 (Boundary sign bound).** Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous
Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Lemma 3.2, p.6 (PDF p.7):
"For V = S ∪̇ T, call a set crossing if it meets both parts. Let B_{S,q} be the submatrix of W_{q,r}
with crossing rows and crossing columns. Lemma 3.2 (Boundary sign bound). For 2 ≤ q ≤ r, every nonzero
real vector h satisfying B_{S,q} h = 0 obeys |{e : h_e > 0}| ≥ 2^{q−1}, |{e : h_e < 0}| ≥ 2^{q−1}."

**Formalization Note.** `V = Fin n`, `T = V ∖ S`; `h` is indexed by the crossing `r`-sets. -/
theorem lemma_3_2 (n q r : ℕ) (hq : 2 ≤ q) (hqr : q ≤ r) (S : Finset (Fin n))
    (h : {e : Finset (Fin n) // e.card = r ∧ IsCrossing S e} → ℝ) (hne : h ≠ 0)
    (hker : (crossingMatrix n q r S).mulVec h = 0) :
    2 ^ (q - 1) ≤ (Finset.univ.filter (fun e => 0 < h e)).card ∧
      2 ^ (q - 1) ≤ (Finset.univ.filter (fun e => h e < 0)).card := by sorry

end HypRecov
