-- Prove2me | Theorems.Thm_JakulinBratko_condI_eq_alternating_sum
-- name    : JakulinBratko.condI_eq_alternating_sum
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:04:18.886347+00:00
-- url     : https://prove2.me/theorems/8ead900b-35e4-41d2-834c-478f4509d659
-- title:
--   §2.3.2 and Eq. (10) — the entropy form of $I(\mathcal R\mid X)$
-- statement:
--   Let $P$ be a joint law, $X$ an attribute and $\mathcal R$ a set of attributes with $X\notin\mathcal R$. Then
--
--   $$
--   I(\mathcal R\mid X)=-\sum_{\mathcal T\subseteq\mathcal R}(-1)^{|\mathcal R|-|\mathcal T|}\bigl(H(\mathcal T\cup\{X\})-H(X)\bigr),
--   $$
--
--   where the left side is the average over $x$ of $I(\mathcal R)$ under the conditional law given $X=x$.
--
--   So conditioning on $X$ replaces each entropy in Eq. (10) by the corresponding conditional entropy. It is this identity that makes the recursion of Eq. (10) a statement with content.
--
--   Differences from the source:
--   - reading: I(R|X), defined by the paper only through I(A; B|C) → the average condI P X R; reason: the paper calls this quantity "expected" (p.7) and "average" (p.14)
--   - generalization: the 2-way case I(X; Y|C) → every R with X ∉ R, including R = ∅; reason: Eq. (10) uses I(S \ X|X) for all k; R = {A, B} gives the printed case
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.3.2, p.7; §2.4, Eq. (10), p.8

import Definitions.Def_JakulinBratko_IsLaw
import Definitions.Def_JakulinBratko_H
import Definitions.Def_JakulinBratko_condI

namespace JakulinBratko

/-- The entropy form of the conditional interaction information (Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.3.2, p.7, and Eq. (10), p.8):
the average of `I(R)` over the conditional laws given `X` is the alternating sum of the conditional
entropies `H(T | X) = H(T ∪ {X}) - H(X)`. -/
theorem condI_eq_alternating_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (hP : IsLaw P)
    (X : ι) (R : Finset ι) (hX : X ∉ R) :
    condI P X R =
      -∑ T ∈ R.powerset, (-1 : ℝ) ^ (R.card - T.card) * (H P (T ∪ {X}) - H P {X}) := by sorry

end JakulinBratko
