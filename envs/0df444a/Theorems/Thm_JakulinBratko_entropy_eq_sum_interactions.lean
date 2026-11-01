-- Prove2me | Theorems.Thm_JakulinBratko_entropy_eq_sum_interactions
-- name    : JakulinBratko.entropy_eq_sum_interactions
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:03:26.831455+00:00
-- url     : https://prove2.me/theorems/934fa365-1d14-40e4-b38b-9854977474aa
-- title:
--   §3.1 — $H(\mathcal S)=-\sum_{\emptyset\ne\mathcal T\subseteq\mathcal S}I(\mathcal T)$
-- statement:
--   Let $P$ be a joint law and $\mathcal S$ a set of attributes. Then
--
--   $$
--   H(\mathcal S)=-\sum_{\emptyset\ne\mathcal T\subseteq\mathcal S}I(\mathcal T).
--   $$
--
--   The singleton terms are the entropies $H(X)=-I(\{X\})$, so the joint entropy is the sum of the attribute entropies minus the sum of the interaction informations of the subsets with at least two elements. This is Möbius inversion of Eq. (10) on the subset lattice, and it is what the paper's information graphs display.
--
--   Differences from the source:
--   - reading: "summing all the gray nodes and subtracting all the white nodes linked to the relevant attributes" → the sum -∑ of I(T) over nonempty T ⊆ S; reason: gray nodes are H(X) = -I({X}) and negative interactions, white nodes positive interactions, so each node enters as -I(T)
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §3.1, p.11

import Definitions.Def_JakulinBratko_IsLaw
import Definitions.Def_JakulinBratko_I

namespace JakulinBratko

/-- §3.1, p.11 (Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3): the joint entropy of any subset of the attributes is recovered from the
interaction informations of its nonempty subsets, `H(S) = -∑_{∅ ≠ T ⊆ S} I(T)`. In the paper's
diagrams the singleton terms are the entropies `H(X) = -I({X})`. -/
theorem entropy_eq_sum_interactions {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (hP : IsLaw P)
    (S : Finset ι) :
    H P S = -∑ T ∈ S.powerset with T ≠ ∅, I P T := by sorry

end JakulinBratko
