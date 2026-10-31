-- Prove2me | Theorems.Thm_MarketMakerAds_proof_theorem_3_allocation
-- name    : MarketMakerAds.proof_theorem_3_allocation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:31:42.75458+00:00
-- url     : https://prove2.me/theorems/504e2ff3-f71d-410e-98e8-019b261f2670
-- title:
--   Proof of Theorem 3 — the clearing price, the allocation and the efficiency are unchanged
-- statement:
--   Let $l$ be a finite list of unit values and $I$ the number of units for sale. Let $c$ be the $(I+1)$-th highest value of $l$, or $0$ if $l$ has at most $I$ entries. Let a predicate $Q$ select some units (those that buy the Market-Maker contract), and suppose every selected unit has value strictly greater than $c$. Write $\ell$ for the number of selected units and $\mathrm{rest}$ for the unselected ones. Then:
--
--   1. $\ell\le I$;
--   2. the $(I-\ell+1)$-th highest value of $\mathrm{rest}$ (or $0$ if it has at most $I-\ell$ entries) equals $c$: the clearing price of the auction for the remaining $I-\ell$ units is unchanged;
--   3. the selected units plus the $I-\ell$ highest units of $\mathrm{rest}$ have the same total value as the $I$ highest units of $l$: the allocated value is unchanged;
--   4. if all values are nonnegative, no sublist of $l$ with at most $I$ entries has a larger total value than the $I$ highest units: the auction allocation is efficient.
--
--   In Theorem 3 the selected units are those with value at least $p_{\max}$, which are almost surely strictly above the clearing price.
--
--   Differences from the source:
--   - generalization: buyers with $v\ge p_{\max}$ choosing the contract in a random market → any predicate selecting units strictly above the $(I+1)$-th highest value, in a fixed list of unit values; reason: these are the only facts the argument uses; Theorem 3 applies it outcome by outcome with the purchase rule.
--   - encoding: buyers with demands $k_j$ → a list of unit values with $k_j$ copies of each buyer's value; reason: the paper's per-unit reduction (Assumption 2, p.11).
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, Proof of Theorem 3, p.18 (clearing price and allocation unchanged) and p.19 ("the outcome is efficient")

import Mathlib
import Definitions.Def_MarketMakerAds_sortDesc

namespace MarketMakerAds

/-- **Proof of Theorem 3, p.18: the clearing price, the allocation and the efficiency are
unchanged.**
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, Proof of Theorem 3,
p.18: "the auction clearing price (in P2) remains the same as in the situation where no
Market-Maker contract was offered (i.e., this is because the highest valued ℓ ≤ I buyers select
the Market-Maker contract in P1 and I − ℓ buyers participate in the auction in P2, the auction
clearing price is still the (I + 1)-th highest value for all ℓ ≤ I), and thus the set of allocated
buyers … remains exactly the same", and p.19: "the outcome is efficient, that is, the
highest-valued I bidders are allocated".

Let `l` be a list of unit values, `I` the number of units, and `c` the `(I+1)`-th highest value
(`0` if `l` has at most `I` entries). Suppose every unit selected by a predicate `Q` (the contract
buyers) has value strictly above `c`. Let `mm` be the selected units, `ℓ` their number, and `rest`
the others. Then
1. `ℓ ≤ I`;
2. the `(I − ℓ + 1)`-th highest value of `rest` (`0` if `rest` has at most `I − ℓ` entries) is `c`;
3. the selected units plus the `I − ℓ` highest units of `rest` have the same total value as the
   `I` highest units of `l`;
4. if all values are nonnegative, no sublist of `l` with at most `I` entries has a larger total
   than the `I` highest units (the auction allocation is efficient).

**Formalization Note** Pure list statement, no probability. In Theorem 3 the hypothesis on `Q` is
delivered almost surely by Corollary 2 and the absence of an atom at `p_max`. -/
theorem proof_theorem_3_allocation (l : List ℝ) (I : ℕ) (Q : ℝ → Prop) [DecidablePred Q]
    (hQ : ∀ x ∈ l, Q x → (sortDesc l).getD I 0 < x) :
    let mm := l.filter fun x => decide (Q x)
    let rest := l.filter fun x => !decide (Q x)
    mm.length ≤ I ∧
    (sortDesc rest).getD (I - mm.length) 0 = (sortDesc l).getD I 0 ∧
    mm.sum + ((sortDesc rest).take (I - mm.length)).sum = ((sortDesc l).take I).sum ∧
    ((∀ x ∈ l, 0 ≤ x) →
      ∀ s : List ℝ, s.Sublist l → s.length ≤ I → s.sum ≤ ((sortDesc l).take I).sum) := by sorry

end MarketMakerAds
