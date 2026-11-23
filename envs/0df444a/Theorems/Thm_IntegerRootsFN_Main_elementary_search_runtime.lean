-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_elementary_search_runtime
-- name    : IntegerRootsFN.Main.elementary_search_runtime
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:14:24.993803+00:00
-- url     : https://prove2.me/theorems/20695f4f-a2c2-44b1-b9de-2871a14d9e54
-- title:
--   Finite-machine run of the elementary recursive search
-- statement:
--   There is one finite deterministic multitape machine which, on the signed dense binary encoding of the truncated polynomial $g$ and its parameters $d,b$, writes the exact list `searchCandidates` produced by the recursive scale search.
--
--   Its uniform running-time bound is
--
--   $$
--   \widetilde O(d^3b^2),
--   $$
--
--   with one positive constant and fixed logarithmic exponents chosen before all inputs. The machine must perform the actual filtering, center splitting, scale halving, final neighboring-integer formation and duplicate removal. The per-test guarantee is supplied by the machine clause of Lemma A.2; this result assembles those tests into the search and accounts for its control and output costs. No semantic coverage, cardinality or total-size assertion is included here.
--
--   **Formalization Note.** The time bound is the literal `Runs` predicate with `softBound`, evaluated at $d=\min(n,b)$ and $b$.
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 13, Proposition A.3, running-time conclusion and search description; p.12 Lemma A.2 supplies the individual Test machine.

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary
import Definitions.Def_IntegerRootsFN_Main_ElementarySearch

set_option autoImplicit false

theorem IntegerRootsFN.Main.elementary_search_runtime :
    ∃ M : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
    ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
      Runs M (polynomialWord (truncate f n b) (min n b) b)
        (integersWord (searchCandidates f n b))
        (softBound C k l (min n b) b ((min n b : ℕ) ^ 3 * (b : ℝ) ^ 2)) := by sorry
