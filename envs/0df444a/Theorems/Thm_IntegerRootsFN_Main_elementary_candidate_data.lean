-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_elementary_candidate_data
-- name    : IntegerRootsFN.Main.elementary_candidate_data
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:32:51.421931+00:00
-- url     : https://prove2.me/theorems/92cb760f-1b77-4627-8163-5508d5b469b7
-- title:
--   Elementary candidate coverage, cardinality and total point size
-- statement:
--   Assume the exact elementary-search guarantee of Proposition A.3. For a valid degree-$n$ integer polynomial with coefficient bound $b$, put $d=\min(n,b)$ and adjoin the three small candidates to the search list:
--
--   $$C=[-1,0,1]\mathbin{+\!\!+}C'.$$
--
--   Then there are uniform natural constants $K_{\mathrm{card}}$ and $K_{\mathrm{size}}$ such that every integer root of $f$ belongs to $C$, and
--
--   $$|C|\le K_{\mathrm{card}}n,\qquad \sum_{c\in C}\left\lceil\log_2(2+|c|)\right\rceil\le K_{\mathrm{size}}b.$$
--
--   Duplicates and nonroots are allowed. The statement isolates the semantic candidate guarantees from the finite-machine running-time obligation. The explicit existential constants may be taken to be $24$ and $150$; these are convenient formal upper bounds, not claimed to be optimal.
--
--   **Formalization Note.** The list is literally `[-1, 0, 1] ++ searchCandidates f n b`, and `pointSize` counts entries with repetitions. The proof uses $d\le n,b$ and $\log_2(d+1)\le b$, the latter following from $d+1\le2^b$ for $b\ge1$.
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 13, Proposition A.3 and proof of Theorem 1.1(a). The displayed uniform bounds are the formal $O(n)$ and $O(b)$ consequences of $|C|\le21d+3$ and the Proposition A.3 aggregate-size estimate, using $d\le n,b$.

import Definitions.Def_IntegerRootsFN_Main_CandidatePipeline

set_option autoImplicit false

namespace IntegerRootsFN.Main

theorem elementary_candidate_data
    (hsearch : ElementarySearchContract) :
    ∃ Kcard Ksize : ℕ,
      ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
        (∀ r : ℤ, f.IsRoot r → r ∈ [-1, 0, 1] ++ searchCandidates f n b) ∧
        ([-1, 0, 1] ++ searchCandidates f n b).length ≤ Kcard * n ∧
        pointSize ([-1, 0, 1] ++ searchCandidates f n b) ≤ Ksize * b := by sorry
