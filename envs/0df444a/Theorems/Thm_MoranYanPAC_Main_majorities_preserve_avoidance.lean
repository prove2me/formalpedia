-- Prove2me | Theorems.Thm_MoranYanPAC_Main_majorities_preserve_avoidance
-- name    : MoranYanPAC.Main.majorities_preserve_avoidance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:07:15.946831+00:00
-- url     : https://prove2.me/theorems/ae06bc26-d05e-4262-9b7d-5281a101bbe7
-- title:
--   Lemma 9 — majorities preserve witness-space avoidance
-- statement:
--   Fix a nonempty $H$ of Littlestone dimension $d\ge1$ and its fixed source witnesses. Let $G\subseteq U$ be a finite nonempty good family and $h\in U$. If every member of $G$ lies outside $Q_h$, then
--
--   $$b_G\notin Q_h.$$
--
--   This is the avoidance property for the same pointwise majority and witness spaces used throughout the candidate construction; the family is good at all domain points, not merely at observed points.
--
--   Differences from the source:
--   - encoding: finite families of distinct predictors → Finset of functions with extensional equality; reason: this represents exactly the source finite sets, independently of repeated observations
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Lemma 9, p. 23 (PDF p. 23)

import Mathlib
import Definitions.Def_MoranYanPAC_Main_Candidates
import Definitions.Def_MoranYanPAC_Main_GoodFamily

set_option autoImplicit false

namespace MoranYanPAC.Main

/-- Lemma 9, p. 23. The source's nonempty good family lies in U. -/
theorem majorities_preserve_avoidance {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw)
    (G : Finset (X → Bool)) (hgood : Good d G)
    (hG : ∀ g ∈ G, g ∈ PrivLittlestone.localUniverse H d)
    (h : X → Bool) (hh : h ∈ PrivLittlestone.localUniverse H d)
    (havoid : ∀ g ∈ G, g ∉ PrivLittlestone.witnessSpace H d Aw h) :
    majority G ∉ PrivLittlestone.witnessSpace H d Aw h := by sorry

end MoranYanPAC.Main
