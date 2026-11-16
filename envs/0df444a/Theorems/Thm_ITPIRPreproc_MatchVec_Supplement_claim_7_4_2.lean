-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_Supplement_claim_7_4_2
-- name    : ITPIRPreproc.MatchVec.Supplement.claim_7_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:52:24.674189+00:00
-- url     : https://prove2.me/theorems/b859fd58-c8fe-4b57-bf78-41539283478f
-- title:
--   Claim 7.4.2 — the majority query is uniform on $\mathcal R$, also conditional on ok; the fail branch has probability at most $1/16$
-- statement:
--   Let $m=2^h$ with $h\ge3$. Fix an integer $H\ge h+64$, with $d=2H^{14}+1$. Fix a seed, and for a target $i=(a^\star,b^\star)\in[m]\times\{-1,+1\}^h$ sample
--   $$R\leftarrow\mathcal R_i,\qquad (Q,u)\leftarrow\mathrm{Query}(i,R).$$
--   Then:
--
--   1. $Q$ is uniform on $\mathcal R$, the branch $u=\mathrm{fail}$ included: $\Pr[Q=Q_0]=1/|\mathcal R|$ for every key $Q_0$;
--   2. conditional on $u=\mathrm{ok}$, $Q$ is also uniform on $\mathcal R$: $\Pr[Q=Q_0,\ u=\mathrm{ok}]=\Pr[u=\mathrm{ok}]/|\mathcal R|$ for every $Q_0$;
--   3. there is a single number $p\le 1/16$ such that for every target $i$ and every key $R\in\mathcal R_i$, $\mathrm{Query}(i,R)$ returns $u=\mathrm{fail}$ with probability exactly $p$.
--
--   This is property (ii) of Definition 4.1 for the majority primitive, and the privacy of Theorem 7.1 rests on it.
--
--   **Formalization Note** Uniformity of $R$ over $\mathcal R_i$ is the average over $\mathcal R_i$ (`avgOver`). Conditional uniformity is stated in product form. By clause 3, $\Pr[u=\mathrm{ok}]\ge15/16>0$, so the product form is equivalent to the conditional statement. Clause 3 is stated for each fixed key, not on average over keys.
--
--   Differences from the source:
--   - encoding: Q ≡ Unif(R) when R ← R_i and (Q, u) ← Query(i, R) → the average over R_i of Pr[Q = Q₀] equals 1/#R for every key Q₀; reason: uniform law on a finite set; same law
--   - encoding: conditional on u = ok, the query is uniform on R → Pr[Q = Q₀ ∧ u = ok] = Pr[u = ok]·(1/#R) for every Q₀; reason: equivalent to the conditional law being uniform, since Pr[u = ok] ≥ 15/16 > 0 by clause 3
--   - encoding: the fail branch has probability at most 1/16, independently of the key and the target → there is one p ≤ 1/16 equal to Pr[u = fail] under Query(i, R) for every target i and every key R ∈ R_i; reason: the literal statement for the fixed seed
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Claim 7.4.2, printed p.28 (PDF p.30); Query algorithm, printed p.27 (PDF p.29)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_Supplement_Majority

open scoped ENNReal

namespace ITPIRPreproc.MatchVec.Supplement

/-- Claim 7.4.2, printed p.28 (PDF p.30). Under the §7.2 parameters, for every seed `σ`:
for every target `i = (a⋆, b⋆)`, with `R ← R_i` and `(Q, u) ← Query(i, R)`,
(1) `Q` is uniform on `R` (the branch `u = fail` included): `Pr[Q = Q₀] = 1/|R|` for every key `Q₀`;
(2) conditional on `u = ok`, `Q` is uniform: `Pr[Q = Q₀ ∧ u = ok] = Pr[u = ok] / |R|`;
(3) there is one number `p ≤ 1/16` such that, for every target `i` and every key `R ∈ R_i`,
`Query(i, R)` returns `u = fail` with probability exactly `p`. (`u = true` is `ok`.) -/
theorem claim_7_4_2 (h H : ℕ) (hh : 3 ≤ h) (hH : h + 64 ≤ H) (σ : Seed h H) :
    (∀ (i : MPos h) (Q₀ : Key h H),
      avgOver (majCompat σ i) (fun R => (majQuery σ i R).toOuterMeasure {p | p.1 = Q₀}) =
        (Fintype.card (Key h H) : ℝ≥0∞)⁻¹) ∧
    (∀ (i : MPos h) (Q₀ : Key h H),
      avgOver (majCompat σ i)
          (fun R => (majQuery σ i R).toOuterMeasure {p | p.1 = Q₀ ∧ p.2 = true}) =
        avgOver (majCompat σ i) (fun R => (majQuery σ i R).toOuterMeasure {p | p.2 = true}) *
          (Fintype.card (Key h H) : ℝ≥0∞)⁻¹) ∧
    (∃ pfail : ℝ≥0∞, pfail ≤ 1 / 16 ∧
      ∀ (i : MPos h) (R : Key h H), R ∈ majCompat σ i →
        (majQuery σ i R).toOuterMeasure {p | p.2 = false} = pfail) := by sorry

end ITPIRPreproc.MatchVec.Supplement
