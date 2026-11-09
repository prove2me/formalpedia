-- Prove2me | Theorems.Thm_MoranYanPAC_Main_majorities_increase_rank
-- name    : MoranYanPAC.Main.majorities_increase_rank
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:05:56.357705+00:00
-- url     : https://prove2.me/theorems/e50aa758-adbb-4bd9-9d30-b88be9c1fbcb
-- title:
--   Lemma 5 — overwhelming majorities increase rank
-- statement:
--   Fix a nonempty $H$ with Littlestone dimension $d\ge1$. Let $0\le s<d$ and let $G\subseteq F_s$ be a finite family of at least two distinct predictors. Suppose at every point fewer than a $1/[2(d+1)]$ fraction disagree with its pointwise majority $b_G$. Then
--
--   $$b_G\in F_{s+1}.$$
--
--   Membership in $F_{s+1}$ includes membership in $U$ and rank at least $s+1$. The hypothesis is strict, including at the threshold; no single-point or sample-only version of majority agreement is substituted.
--
--   Differences from the source:
--   - encoding: finite families of distinct predictors → Finset of functions with extensional equality; reason: this represents exactly the source finite sets, independently of repeated observations
--   - encoding: strict pointwise disagreement fraction <1/[2(d+1)] → 2(d+1) times the minority count is less than the family size; reason: the denominator and family size are positive
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Lemma 5, p. 20 (PDF p. 20)

import Mathlib
import Definitions.Def_PrivLittlestone_rankLayer
import Definitions.Def_MoranYanPAC_Main_GoodFamily

set_option autoImplicit false

namespace MoranYanPAC.Main

/-- Lemma 5, p. 20: strict overwhelming majority, distinct predictors. -/
theorem majorities_increase_rank {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (s : ℕ) (hs : s < d) (G : Finset (X → Bool)) (hcard : 2 ≤ G.card)
    (hG : ∀ h ∈ G, h ∈ PrivLittlestone.rankLayer H d s) (hgood : Good d G) :
    majority G ∈ PrivLittlestone.rankLayer H d (s + 1) := by sorry

end MoranYanPAC.Main
