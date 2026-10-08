-- Prove2me | Theorems.Thm_GoldbachComet_orderedReprCount_eq_card
-- name    : GoldbachComet.orderedReprCount_eq_card
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T05:29:35.471382+00:00
-- url     : https://prove2.me/theorems/a8640211-2336-46f1-9d4e-3eb5a724877d
-- title:
--   Ordered Goldbach count as left-prime cardinality
-- statement:
--   ## Statement
--
--   For every natural number `n`, the number of ordered Goldbach representations equals the cardinality of the left-prime finset:
--
--   \[
--   r_{\mathrm{ord}}(n) = \bigl|\{ p \in \{0,\ldots,n\} : 2 \le p,\ 2 \le n-p,\ p\ \text{prime},\ n-p\ \text{prime}\}\bigr|.
--   \]
--
--   Formally: `GoldbachComet.orderedReprCount n = (GoldbachComet.primeLeftSummand n).card`.
--
--   ## Proof idea
--
--   By definition, `orderedReprCount n` is the cardinality of `orderedReprPairs n`, which is `(primeLeftSummand n).map (pairEmbedding n)`. The map `pairEmbedding n` is injective on its domain, so `Finset.card_map` gives equality with `(primeLeftSummand n).card`.
--
--   ## Role in the imprint program
--
--   This is the direct cardinality form of the pairing lemma (M1a). Together they identify `r_{\mathrm{ord}}(n)` with a sum over left primes, which is the discrete backbone for Hardy–Littlewood–type expansions and prime-race corrections.
--
--   ## References
--
--   - Same counting conventions as `Definitions/Def_GoldbachComet.lean`.
--   - Empirical motivation: `docs/captain/goldbach/FRESH-PERSPECTIVES-2026-10-04.md` (D4).
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

namespace GoldbachComet

theorem orderedReprCount_eq_card (n : ℕ) :
    orderedReprCount n = (primeLeftSummand n).card := by sorry

end GoldbachComet
