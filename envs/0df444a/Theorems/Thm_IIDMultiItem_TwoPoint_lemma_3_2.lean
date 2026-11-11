-- Prove2me | Theorems.Thm_IIDMultiItem_TwoPoint_lemma_3_2
-- name    : IIDMultiItem.TwoPoint.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:58:28.362112+00:00
-- url     : https://prove2.me/theorems/bb3c48d8-7ee0-4c4a-9a31-baa2e18d6559
-- title:
--   Lemma 3.2 (bundle prices) — what one buyer receives and pays at Q ∪ T, and Θ(Q) ≤ Θ(Q′) + |Q′ \ Q| (any integer reserves)
-- statement:
--   Let $0<a<b$, $\Delta=b-a$, and let $\theta_0,\theta_1,\dots$ be any integer reserves. Fix buyer $i$ and the reports of the others; let $H$, $D=[m]\setminus H$, $d=|D|$ and $\Theta(Q)$ be as in §3.2. Let buyer $i$ report $Q\cup T$ with $Q\subseteq H$, $T\subseteq D$, $r=|T|$.
--   1. If $r<\Theta(Q)$, buyer $i$ receives $T$ together with the items of $Q$ that no buyer ranked before her reports high, and pays $b$ for each of them.
--   2. If $r\ge\Theta(Q)$, buyer $i$ receives $D\cup Q$ and pays $ad+b|Q|+\Delta\,\Theta(Q)$.
--
--   Moreover, for all $Q,Q'\subseteq H$,
--   $$\Theta(Q)\le\Theta(Q')+|Q'\setminus Q|.\tag{3.5}$$
--
--   On $D$ the buyer thus faces bundle prices; (3.5) is what makes misreporting on $H$ unprofitable in Proposition 3.5.
--
--   Differences from the source:
--   - encoding: integer reserves θ_0, …, θ_m → θ : ℕ → ℤ (values beyond m are never used); reason: the paper states the lemma for any integer reserves; every finite sequence extends to such a θ
--   - encoding: Θ(Q), the threshold (3.4) at the report Q ∪ T → ThetaQ θ S i Q = max({θ_{|D|}} ∪ {|C_ℓ \ Q| + 1{ℓ < i} : ℓ ≠ i}); reason: the paper's own description (e_ℓ(Q) = |C_ℓ \ Q|, d = c + e_i = |D|); it does not depend on T
--   - encoding: reports v_{-i} of the other buyers → a full profile v whose coordinate i is ignored (buyer i's report enters through Function.update v i t); reason: Lean convention; every v_{-i} is obtained and nothing depends on v i
--   - generalization: m ≥ 1 (§2.1: items [m] for a positive integer m), a buyer i among n ≥ 1 → any m ∈ ℕ (n = 0 leaves no buyer i, so the statement is vacuous there); reason: at m = 0, Q = T = ∅, A_i = ∅ and the payment is −∆[−Θ]_+, which is 0 if Θ > 0 and ∆Θ if Θ ≤ 0, as (1) and (2) say; for m ≥ 1 it is the paper's statement
-- source:
--   Liu, Liu, Wang, Optimal Multi-Item Auctions with I.I.D. Values, arXiv:2610.11051 (held version, PDF of 2026-11-03, sha256 983080a4…), p. 14 (PDF 16), Lemma 3.2; p. 38 (PDF 40), §B.3

import Mathlib
import Definitions.Def_IIDMultiItem_TwoPoint_Counts
import Definitions.Def_IIDMultiItem_TwoPoint_Auction

namespace IIDMultiItem.TwoPoint

/-- Lemma 3.2 (bundle prices), for any integer reserves `θ`. Fix buyer `i` and the others'
reports (the coordinates `ℓ ≠ i` of `S`), let buyer `i` report `Q ∪ T` with `Q ⊆ H`, `T ⊆ D`,
`r = |T|`. (1) If `r < Θ(Q)`, she receives `T` together with the items of `Q` that no buyer
ranked before her reports high, and pays `b` for each of them. (2) If `r ≥ Θ(Q)`, she receives
`D ∪ Q` and pays `a d + b |Q| + ∆ Θ(Q)`. Moreover `Θ(Q) ≤ Θ(Q') + |Q' \ Q|` for all
`Q, Q' ⊆ H` (3.5). -/
theorem lemma_3_2 {n m : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b) (θ : ℕ → ℤ)
    (S : Fin n → Finset (Fin m)) (i : Fin n) :
    (∀ Q T : Finset (Fin m), Q ⊆ oppHigh S i → T ⊆ oppLow S i →
      let S' := Function.update S i (Q ∪ T)
      ((T.card : ℤ) < ThetaQ θ S i Q →
        alloc θ S' i = T ∪ (Q ∩ unclaimed S' i) ∧
        payment a b θ S' i = b * (alloc θ S' i).card) ∧
      (ThetaQ θ S i Q ≤ (T.card : ℤ) →
        alloc θ S' i = oppLow S i ∪ Q ∧
        payment a b θ S' i =
          a * (oppLow S i).card + b * Q.card + (b - a) * (ThetaQ θ S i Q : ℝ))) ∧
    ∀ Q Q' : Finset (Fin m), Q ⊆ oppHigh S i → Q' ⊆ oppHigh S i →
      ThetaQ θ S i Q ≤ ThetaQ θ S i Q' + ((Q' \ Q).card : ℤ) := by sorry

end IIDMultiItem.TwoPoint
