-- Prove2me | Theorems.Thm_GroupLabeledMatroid_Proximity_color_rank_drop
-- name    : GroupLabeledMatroid.Proximity.color_rank_drop
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:01.605803+00:00
-- url     : https://prove2.me/theorems/fd1b160c-6be9-461f-921a-5e9f3628178d
-- title:
--   Lemma 17 — exact color-rank drop
-- statement:
--   Let $M$ have positive rank and ground $E=A\mathbin{\dot\cup}B$, where $A$ is a minimum-cost base and $B$ is the unique minimum-cost base in its label fiber. Costs are arbitrary reals, labels lie in an arbitrary abelian group, and equal element costs are allowed. Order $B$ by nondecreasing cost. For every $i\in[r]$ and color $h\in G$, the exact drop in color rank is
--
--   $$r_i(E_h^i)-r_{i+1}(E_h^{i+1})=\mathbf1_{\{h\in H_i\}}.$$
--
--   This retains the equality and the indicator, including the last contraction. It relates color ranks to the threshold-label growth count.
--
--   Differences from the source:
--   - encoding: finite ground set E and finite subsets → Finset subsets of a finite ambient type with classical decidable equality, genuine Mathlib ground M.E, and finite natural ranks; reason: every finite source ground admits this representation; arbitrary subsets M.E support minors; finite rank conversion has no infinite case; classical equality imposes no restriction on the label group
--   - encoding: indices i=1,…,r and terminal stage r+1 → i : Fin r represents source i+1; natural stage k represents source k+1; H is filtered over occurring ground labels; reason: prefix k contracts the first k base elements, stage r is terminal, and a nonloop pivot cannot be spanned by an empty color class, so filtering H changes no member
--   - encoding: integer rank difference equals an indicator → rank before = rank after + indicator, using finite natural ranks; reason: equivalent exact equality without truncating a negative difference
-- source:
--   Siyue Liu, Taihei Oki, Chao Xu, Proximity Theorem and FPT Algorithm for Minimum Group-labeled Matroid Bases, STOC 2027 submission #554 (October 2026), p. 9, Lemma 17, Eq. (2); standing hypotheses and definitions pp. 6–8

import Definitions.Def_GroupLabeledMatroid_Proximity_ContractionFiltration
open scoped Pointwise

namespace GroupLabeledMatroid.Proximity

theorem color_rank_drop {E G : Type*} [Fintype E] [DecidableEq E] [AddCommGroup G] [DecidableEq G]
    (M : Matroid E) (ℓ : E → G) (c : E → ℝ) (A B : Finset E)
    (hblock : IsBlockPair M ℓ c A B) {r : ℕ} (hr : 0 < r)
    (b : Fin r → E) (horder : IsCostOrder c B b) (i : Fin r) (h : G) :
    rankOn (stageMinor M b i.val) (stageColor M ℓ b i.val h) =
      rankOn (stageMinor M b (i.val + 1)) (stageColor M ℓ b (i.val + 1) h) +
        (if h ∈ stageH M ℓ c b i then 1 else 0) := by sorry

end GroupLabeledMatroid.Proximity
