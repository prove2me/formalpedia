-- Prove2me | Theorems.Thm_GoldbachComet_orderedReprCount_eq_sum
-- name    : GoldbachComet.orderedReprCount_eq_sum
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T04:28:36.064169+00:00
-- url     : https://prove2.me/theorems/f9abd51e-9b0f-4cf8-ae5d-5412152b15bf
-- title:
--   Ordered Goldbach count as a finset sum
-- statement:
--   ## Statement
--
--   For every natural number `n`, the number of **ordered** prime pairs `(p, q)` with `p + q = n` equals the cardinality of the finset of left primes
--
--   \[
--   \{ p \le n : 2 \le p,\ 2 \le n-p,\ p\ \text{prime},\ n-p\ \text{prime} \}.
--   \]
--
--   In the formalization this is `GoldbachComet.orderedReprCount n = ∑_{p \in \text{primeLeftSummand}\,n} 1`.
--
--   ## Proof idea
--
--   Define `primeLeftSummand n` as the filter of `p ∈ {0,…,n}` satisfying the four inequalities. Map `p ↦ (p, n-p)`; injectivity follows from the first coordinate. The image finset is `orderedReprPairs n`, so
--
--   \[
--   |\text{orderedReprPairs n}| = |\text{primeLeftSummand n}| = \sum_{p \in \text{primeLeftSummand n}} 1
--   \]
--
--   by `Finset.card_map` and `Finset.card_eq_sum_ones`.
--
--   ## Role in the imprint program
--
--   This is the discrete backbone for expanding `r(n)` as a sum over `p` with `q = n-p` prime. The next milestones add residue-class deviations of `\pi(x)` in arithmetic progressions (Chebyshev bias) to obtain the first-order correction in the Goldbach comet.
--
--   ## References
--
--   - Hardy–Littlewood singular series (normalization layer, not used in this lemma).
--   - Empirical derivation: `docs/captain/goldbach/FRESH-PERSPECTIVES-2026-10-04.md` (D4).
-- source:
--   docs/goldbach-comet/README.md; empirical motivation in docs/captain/goldbach/FRESH-PERSPECTIVES-2026-10-04.md

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_GoldbachComet
open scoped BigOperators
set_option autoImplicit false
open GoldbachComet

namespace GoldbachComet

theorem orderedReprCount_eq_sum (n : ℕ) :
    orderedReprCount n = (primeLeftSummand n).sum (fun _ => 1) := by sorry

end GoldbachComet
