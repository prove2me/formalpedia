-- Prove2me | Theorems.Thm_MoranYanPAC_Main_global_local_candidate_counts
-- name    : MoranYanPAC.Main.global_local_candidate_counts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T03:07:17.64033+00:00
-- url     : https://prove2.me/theorems/23c409f2-235c-4f0c-bbe0-9958ee2780f6
-- title:
--   Lemma 11 — global, local and total candidate counts (extends referenced layer counts)
-- statement:
--   Fix a nonempty $H$ with Littlestone dimension $d\ge1$ and the sample-independent source witnesses. For every sample $S$, every nonempty cell $V=V_v(S)$ and every $0\le s\le d$,
--
--   $$|T_s(V)|\le[2(d+1)]^{d-s}.$$
--
--   For every $h\in U$ of rank $r\ge s$,
--
--   $$|T_s(V)\cap Q_h|\le[2(d+1)]^{r-s}.$$
--
--   The candidate set $C(S)$ is finite on every finite input. If $n=|S|\ge d$, then also
--
--   $$|C(S)|\le2[2(d+1)]^d(en/d)^d.$$
--
--   The referenced Open layer-count core gives the first two inequalities. This full canonical extension retains both and adds the total bound, together with the finiteness they express. Its hypotheses do not assume counts, finiteness, or realizability of $S$.
--
--   Differences from the source:
--   - encoding: cardinalities of selected sets, including the finiteness implicit in the bounds → extended natural cardinalities for layer counts and explicit finiteness before the real total count; reason: an infinite selected set cannot satisfy a finite bound by receiving the junk natural cardinality zero
-- source:
--   Shay Moran, Chao Yan, STOC 2027 submission #772 (October 2026), Lemma 11, p. 24 (PDF p. 24)

import Mathlib
import Definitions.Def_MoranYanPAC_Main_Candidates

set_option autoImplicit false

namespace MoranYanPAC.Main

/-- Lemma 11, p. 24. Full extension of the referenced two-count core, retaining
both layer bounds and adding the total bound; no finiteness certificate is assumed. -/
theorem global_local_candidate_counts {X : Type*} (H : Set (X → Bool)) (d : ℕ)
    (hH : H.Nonempty) (hd : UnderstandingML.ldim H = d) (hd1 : 1 ≤ d)
    (Aw : (X → Bool) → Finset X) (hAw : SourceWitnesses H d Aw) (S : List (X × Bool)) :
    (∀ v : Fin S.length → Bool, (PrivLittlestone.versionCell H d S v).Nonempty →
      (∀ s : ℕ, s ≤ d →
        (PrivLittlestone.selT H d Aw (PrivLittlestone.versionCell H d S v) s).encard ≤
          (((2 * (d + 1)) ^ (d - s) : ℕ) : ℕ∞)) ∧
      (∀ h ∈ PrivLittlestone.localUniverse H d, ∀ s : ℕ,
        s ≤ PrivLittlestone.rankOf H d h →
        (PrivLittlestone.selT H d Aw (PrivLittlestone.versionCell H d S v) s ∩
          PrivLittlestone.witnessSpace H d Aw h).encard ≤
            (((2 * (d + 1)) ^ (PrivLittlestone.rankOf H d h - s) : ℕ) : ℕ∞))) ∧
    (candidates H d Aw S).Finite ∧
    (d ≤ S.length → ((candidates H d Aw S).ncard : ℝ) ≤
      2 * (2 * ((d : ℝ) + 1)) ^ d * (Real.exp 1 * S.length / d) ^ d) := by sorry

end MoranYanPAC.Main
