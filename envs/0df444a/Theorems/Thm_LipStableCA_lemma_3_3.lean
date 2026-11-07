-- Prove2me | Theorems.Thm_LipStableCA_lemma_3_3
-- name    : LipStableCA.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:25.985614+00:00
-- url     : https://prove2.me/theorems/f3ee4da7-8fbf-4ef8-8a60-bc57de58f5dd
-- title:
--   Lemma 3.3 — the Lipschitz constant of Mechanism 1
-- statement:
--   For Mechanism 1 with $\tau=-\frac12\log(1-\epsilon)$,
--   $$\mathrm{Lip}(S)\le\frac{15m}{8\tau}\le\frac{15}{4\epsilon}m.$$
--
--   **Formalization Note.** The bound is proved with $|\bigcup_{i\in J}Q_i|$ in place of $m$, for a participant set $J$, since this is what the proof of Lemma 5.8 applies ("with the item set $Y_i$ in place of $M$"). As $|\bigcup_{i\in J}Q_i|\le m$, the printed bound follows.
--
--   Differences from the source:
--   - encoding: profiles of known single-minded bidders with $d(v,w)=\sum_i\mathrm{ld}(v_i,w_i)$ (p.9) → nonnegative scalar reports, the distance `scalarDist J`, and the law `scalarLaw` of Mechanism 1 over the weights; reason: Mechanism 1's input is scalars (p.10) and $\delta_i(v,w)=\mathrm{ld}(v_i,w_i)$ (p.9); with `J = univ` this is the printed $d$
--   - generalization: Mechanism 1 on all bidders $N$ → a participant set $J$, with $\mathcal F_Q$ restricted to subsets of $J$; `J = univ` is the printed mechanism; reason: Mechanism 3 runs it on a subset of the bidders (Lemma 5.8, p.26)
--   - generalization: $15m/(8\tau)$ → $15|\bigcup_{i\in J}Q_i|/(8\tau)$, together with the inequality to $15m/(8\tau)$; reason: Lemma 5.8 applies the lemma with $|Y_i|$ for $m$; the chain specializes to the printed bound
--   - encoding: the paper does not name a σ-algebra on the seed space → measurability of the rule stated as a clause or a hypothesis; reason: this is what makes the allocation law meaningful (paper.md decision 3)
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Lemma 3.3, p.10

import Definitions.Def_LipStableCA_weightedVCG
open MeasureTheory

namespace LipStableCA

/-- **Lemma 3.3.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.10. **Formalization Note.** `ScalarTruthful` on nonnegative reals, with utility `v_i1{i∈ I^*}-p_i`: Mechanism 1's input is scalars (p.10); it also covers `Q_i=∅`. a participant set `J`, with `F_Q` restricted to subsets of `J`; `J = univ` is the printed mechanism: Mechanism 3 runs it on a subset of the bidders (Lemma 5.8, p.26). `15|⋃_{i∈ J}Q_i|/(8τ)`, together with the inequality to `15m/(8τ)`: Lemma 5.8 applies the lemma with `|Y_i|` for `m`; the chain specializes to the printed bound. measurability of the rule stated as a clause or a hypothesis: this is what makes the allocation law meaningful (paper.md decision 3). -/
theorem lemma_3_3 {n m : ℕ} (ord : LinearOrder (Finset (Fin n))) (Q : Fin n → Finset (Fin m)) (J : Finset (Fin n))
    {ϵ : ℝ} (h0 : 0 < ϵ) (h1 : ϵ < 1) :
    (∀ v : Fin n → ℝ, Measurable fun z : Fin n → ℝ => scalarAlloc ord Q J (tauOf ϵ) z v) ∧
    (∀ v w : Fin n → ℝ, (∀ h, 0 ≤ v h) → (∀ h, 0 ≤ w h) → scalarDist J v w ≠ ⊤ →
      emd (scalarLaw ord Q J ϵ v) (scalarLaw ord Q J ϵ w) ≤
        15 * ((J.biUnion Q).card : ℝ) / (8 * tauOf ϵ) * (scalarDist J v w).toReal) ∧
    15 * ((J.biUnion Q).card : ℝ) / (8 * tauOf ϵ) ≤ 15 * (m : ℝ) / (8 * tauOf ϵ) ∧
    15 * (m : ℝ) / (8 * tauOf ϵ) ≤ 15 / (4 * ϵ) * (m : ℝ) := by sorry

end LipStableCA
