-- Prove2me | Theorems.Thm_HousingImprove_distinct_improvers
-- name    : HousingImprove.distinct_improvers
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:27:47.166364+00:00
-- url     : https://prove2.me/theorems/af0959a8-0ac6-4efa-b8ab-af0fc80c2030
-- title:
--   The improving agents may be taken distinct (corrected: clause (iii) of an improvement)
-- statement:
--   Let $H$ and $H'$ be housing markets on a finite agent set $N$ and let $p\in N$.
--
--   1. $H'$ is a $p$-improvement of $H$ if and only if $\prec'_p=\prec_p$ and, for every agent $q\neq p$, the orders $\prec_q$ and $\prec'_q$ satisfy clauses (i)–(iii) of a $(p,q)$-improvement:
--   $$a\prec'_q b\iff a\prec_q b\ (a,b\neq p),\qquad a\prec_q p\Rightarrow a\prec'_q p,\qquad p\prec'_q a\Rightarrow p\prec_q a.$$
--   2. Every $p$-improvement of $H$ is obtained from $H$ by a sequence of $(p,q_i)$-improvements in which the agents $q_1,\dots,q_k$ are pairwise distinct.
--
--   This is what lets the algorithm treat the improving agents one at a time, each once.
--
--   Differences from the source:
--   - correction: a (p,q)-improvement satisfies (i) a ≺′_q b ⇔ a ≺_q b for a, b ≠ p, and (ii) a ≺_q p ⇒ a ≺′_q p (p.9) → IsImprovementAt adds clause (iii): p ≺′_q a ⇒ p ≺_q a for every a; reason: with (i) and (ii) only, Theorem 2 is false: N = {p, q, a}, p ranks q above a above p, a ranks q above a with p unacceptable, q has p and a incomparable above q in H and a above p above q in H′; the swap (p q) is in the core of H and every core allocation of H′ gives p the house of a or her own (proved in the verification file); for strict orders (iii) follows from (ii)
--   - reading: a (p,q)-improvement for agents p and q (q = p not excluded) → q ≠ p; reason: p.12 says the preferences of p remain unchanged; with q = p the theorem fails (N = {p, b}, p raises her own house above b's: the swap is in the core of H, the only core allocation of H′ gives p her own house)
--   - reading: a sequence of (p,q_i)-improvements for some k ∈ ℕ → a list of any length, k = 0 (H′ = H) included; reason: whether 0 ∈ ℕ is not fixed by the paper; for k = 0 every statement holds with X′ = X
--   - encoding: a housing market on a finite agent set N → [Fintype N]; reason: same instances
--   - generalization: we can assume w.l.o.g. that the agents q_1, …, q_k are all distinct (p.11) → part 2 (a Nodup list exists) and, in addition, part 1: H′ is a p-improvement of H iff ≺′_p = ≺_p and every q ≠ p satisfies clauses (i)–(iii) between ≺_q and ≺′_q; reason: part 2 is the page's claim; part 1 is the characterization behind it, added as a conjunct; dropping it gives the source's statement
-- source:
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, §4.1, p.11 ("Observe that we can assume w.l.o.g. that the agents q1, . . . , qk are all distinct.")

import Mathlib
import Definitions.Def_HousingImprove_IsPImprovement

namespace HousingImprove

universe u

/-- **The improving agents may be taken distinct** (Schlotter, Biró, Fleiner,
arXiv:2110.06875v3, §4.1, p.11): "Let `q₁, …, q_k` denote the agents for which `H'` can be obtained
from `H` by a series of `(p, q_i)`-improvements, `i = 1, …, k`. Observe that we can assume w.l.o.g.
that the agents `q₁, …, q_k` are all distinct."

For a finite agent set: (1) `H'` is a `p`-improvement of `H` if and only if `p`'s preferences are
unchanged and every agent `q ≠ p` satisfies clauses (i)–(iii) of a `(p, q)`-improvement between its
orders in `H` and `H'`; (2) every `p`-improvement is obtained along a sequence of pairwise distinct
agents.

**Formalization Note.** `(p, q)`-improvements carry the corrected clause (iii) and `q ≠ p`
(`IsImprovementAt`). -/
theorem distinct_improvers {N : Type u} [Fintype N] (p : N) (H H' : Market N) :
    (IsPImprovement p H H' ↔
      H'.lt p = H.lt p ∧
      ∀ q, q ≠ p →
        (∀ a b, a ≠ p → b ≠ p → (H'.lt q a b ↔ H.lt q a b)) ∧
        (∀ a, H.lt q a p → H'.lt q a p) ∧
        (∀ a, H'.lt q p a → H.lt q p a)) ∧
    (IsPImprovement p H H' → ∃ qs : List N, qs.Nodup ∧ ImprovesAlong p qs H H') := by sorry

end HousingImprove
