-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_elementary_search_coverage
-- name    : IntegerRootsFN.Main.elementary_search_coverage
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:42:23.865669+00:00
-- url     : https://prove2.me/theorems/cab4d51f-307e-4c6d-98c1-96d42c27b610
-- title:
--   Elementary recursive search retains every large integer root
-- statement:
--   For a valid integer polynomial $f$ and an integer root $r$ with $|r|\ge2$, the actual recursively generated deduplicated candidate list `searchCandidates` contains $r$. Starting at the singleton disc centred at $0$, radius $2^b$ contains $r$. At scale $2^{j+1}$, Lemma A.2 prevents the current centre from being discarded, since the nearby root supplied by Lemma 2.2 lies at distance less than $2+2^{j+1}$ from it; one of its two children is within $2^j$ of $r$. Passing from fuel $j+1$ to $j$ therefore preserves the invariant, and the final radius-$1$ candidates include $r$. The case $d=n$ is immediate because the truncation equals $f$.
-- source:
--   Yansong Feng and Itamar Nir, STOC 2027 submission #1353 (October 2026), p.13, proof of Proposition A.3, first paragraph (initial scale, descendant completeness and final integer candidates); uses Lemma A.2 on p.12 and Lemma 2.2 on p.5.

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary
import Definitions.Def_IntegerRootsFN_Main_ElementarySearch

set_option autoImplicit false

theorem IntegerRootsFN.Main.elementary_search_coverage :
    ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      ∀ r : ℤ, f.IsRoot r → 2 ≤ |r| →
        r ∈ searchCandidates f n b := by sorry
