-- Prove2me | Theorems.Thm_LipStableCA_theorem_3_5
-- name    : LipStableCA.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:18.493375+00:00
-- url     : https://prove2.me/theorems/1ce25562-5a16-4b39-898f-d2a8655c1e92
-- title:
--   Theorem 3.5 — Mechanism 1 is UT, ex-post IR, $(1-\epsilon)$-approximate with Lipschitz constant $O(m/\epsilon)$
-- statement:
--   The randomly weighted VCG auction (Mechanism 1) is universally truthful, ex-post individually rational, and $(1-\epsilon)$-approximate, with Lipschitz constant $O(m/\epsilon)$. The welfare guarantee holds at every vector of weights $z\in[-1,1]^n$:
--   $$\sum_{i\in I^*}v_i\ge(1-\epsilon)\max_{I\in\mathcal F_Q}\sum_{i\in I}v_i.$$
--
--   Observation 5.10 applies this welfare guarantee run by run. The matching lower bound for known single-minded bidders (Proposition 3.6) is a separate result and is not part of this mission.
--
--   Differences from the source:
--   - encoding: reports are the scalars of known single-minded bidders, and a bidder's utility is her value for $Q_i$ if she is a winner, minus her payment → `ScalarTruthful` on nonnegative reals, with utility $v_i\mathbf 1\{i\in I^*\}-p_i$; reason: Mechanism 1's input is scalars (p.10); it also covers $Q_i=\emptyset$
--   - generalization: Mechanism 1 on all bidders $N$ → a participant set $J$, with $\mathcal F_Q$ restricted to subsets of $J$; `J = univ` is the printed mechanism; reason: Mechanism 3 runs it on a subset of the bidders (Lemma 5.8, p.26)
--   - generalization: universally truthful and ex-post IR, that is, at every $Z\in[-1,1]^n$ (Lemma 3.2) → truthful and ex-post IR at every real weight vector $z$; reason: the printed proof uses only $e^{\tau z_i}>0$; it specializes to the support $[-1,1]^n$
--   - generalization: $(1-\epsilon)$-approximate in expectation → the guarantee at every $z\in[-1,1]^n$, as the printed proof shows; $\max_{I\in\mathcal F_Q}\sum_{i\in I}v_i$ is $\mathrm{OPT}(v)$ by Observation 3.1; reason: it specializes to the expected-welfare form, and Observation 5.10 needs this strength
--   - encoding: $O(m/\epsilon)$ → the constant $15/4$ of Lemma 3.3; reason: it implies the $O(\cdot)$ form
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Theorem 3.5, p.11

import Definitions.Def_LipStableCA_weightedVCG

namespace LipStableCA

/-- **Theorem 3.5.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.11. **Formalization Note.** `ScalarTruthful` on nonnegative reals, with utility `v_i1{i∈ I^*}-p_i`: Mechanism 1's input is scalars (p.10); it also covers `Q_i=∅`. a participant set `J`, with `F_Q` restricted to subsets of `J`; `J = univ` is the printed mechanism: Mechanism 3 runs it on a subset of the bidders (Lemma 5.8, p.26). the guarantee at every `z∈[-1,1]^n`, as the printed proof shows; `max_{I∈F_Q}Σ_{i∈ I}v_i` is `OPT(v)` by Observation 3.1: it specializes to the expected-welfare form, and Observation 5.10 needs this strength. the constant `15/4` of Lemma 3.3: it implies the `O(·)` form. -/
theorem theorem_3_5 {n m : ℕ} (ord : LinearOrder (Finset (Fin n))) (Q : Fin n → Finset (Fin m)) (J : Finset (Fin n))
    {ϵ : ℝ} (h0 : 0 < ϵ) (h1 : ϵ < 1) :
    (∀ z : Fin n → ℝ, ScalarTruthful (fun v => winnerSet ord Q J (tauOf ϵ) z v)
        (fun v => scalarPay ord Q J (tauOf ϵ) z v)) ∧
    (∀ (z v : Fin n → ℝ), (∀ h, 0 ≤ v h) → ∀ i,
      0 ≤ (if i ∈ winnerSet ord Q J (tauOf ϵ) z v then v i else 0) - scalarPay ord Q J (tauOf ϵ) z v i) ∧
    (∀ z : Fin n → ℝ, (∀ i, z i ∈ Set.Icc (-1 : ℝ) 1) → ∀ v : Fin n → ℝ, (∀ h, 0 ≤ v h) →
      ∀ I ∈ feasibleFamily Q J, (1 - ϵ) * ∑ i ∈ I, v i ≤ ∑ i ∈ winnerSet ord Q J (tauOf ϵ) z v, v i) ∧
    (∀ v w : Fin n → ℝ, (∀ h, 0 ≤ v h) → (∀ h, 0 ≤ w h) → scalarDist J v w ≠ ⊤ →
      emd (scalarLaw ord Q J ϵ v) (scalarLaw ord Q J ϵ w) ≤
        15 / 4 * ((m : ℝ) / ϵ) * (scalarDist J v w).toReal) := by sorry

end LipStableCA
