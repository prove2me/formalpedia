-- Prove2me | Theorems.Thm_LipStableCA_lemma_3_2
-- name    : LipStableCA.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:40.199186+00:00
-- url     : https://prove2.me/theorems/1f7c2109-7dd0-4002-a77b-00c6a1b2cdb1
-- title:
--   Lemma 3.2 — Mechanism 1 is universally truthful and ex-post IR
-- statement:
--   The randomly weighted VCG auction (Mechanism 1) with public desired bundles $Q_1,\dots,Q_n$ and $0<\epsilon<1$ is universally truthful and ex-post individually rational. That is, for every fixed vector of weights $z$, reporting her true value maximizes a bidder's utility and her utility is nonnegative. Moreover, the payments are nonnegative.
--
--   For fixed weights, the mechanism is a VCG mechanism on the weighted bids.
--
--   Differences from the source:
--   - encoding: reports are the scalars of known single-minded bidders, and a bidder's utility is her value for $Q_i$ if she is a winner, minus her payment → `ScalarTruthful` on nonnegative reals, with utility $v_i\mathbf 1\{i\in I^*\}-p_i$; reason: Mechanism 1's input is scalars (p.10); it also covers $Q_i=\emptyset$
--   - generalization: Mechanism 1 on all bidders $N$ → a participant set $J$, with $\mathcal F_Q$ restricted to subsets of $J$; `J = univ` is the printed mechanism; reason: Mechanism 3 runs it on a subset of the bidders (Lemma 5.8, p.26)
--   - generalization: $Z\in[-1,1]^n$ → every real weight vector $z$; reason: the printed proof uses only $e^{\tau z_i}>0$; it specializes to $[-1,1]^n$
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Lemma 3.2, p.10

import Definitions.Def_LipStableCA_weightedVCG

namespace LipStableCA

/-- **Lemma 3.2.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.10. **Formalization Note.** `ScalarTruthful` on nonnegative reals, with utility `v_i1{i∈ I^*}-p_i`: Mechanism 1's input is scalars (p.10); it also covers `Q_i=∅`. a participant set `J`, with `F_Q` restricted to subsets of `J`; `J = univ` is the printed mechanism: Mechanism 3 runs it on a subset of the bidders (Lemma 5.8, p.26). every real weight vector `z`: the printed proof uses only `e^{τ z_i}>0`; it specializes to `[-1,1]^n`. -/
theorem lemma_3_2 {n m : ℕ} (ord : LinearOrder (Finset (Fin n))) (Q : Fin n → Finset (Fin m)) (J : Finset (Fin n))
    {ϵ : ℝ} (h0 : 0 < ϵ) (h1 : ϵ < 1) (z : Fin n → ℝ) :
    ScalarTruthful (fun v => winnerSet ord Q J (tauOf ϵ) z v) (fun v => scalarPay ord Q J (tauOf ϵ) z v) ∧
    ∀ v : Fin n → ℝ, (∀ h, 0 ≤ v h) → ∀ i,
      0 ≤ (if i ∈ winnerSet ord Q J (tauOf ϵ) z v then v i else 0) - scalarPay ord Q J (tauOf ϵ) z v i ∧
        0 ≤ scalarPay ord Q J (tauOf ϵ) z v i := by sorry

end LipStableCA
