-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_Supplement_claim_7_4_3
-- name    : ITPIRPreproc.MatchVec.Supplement.claim_7_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:53:04.093615+00:00
-- url     : https://prove2.me/theorems/304869a2-10fe-4215-99f0-a25a75decac6
-- title:
--   Claim 7.4.3 — the majority decoder never errs, and for a good seed recovers $D[a^\star,b^\star]$ with probability at least $5/8$
-- statement:
--   Let $m=2^h$ with $h\ge3$. Fix an integer $H\ge h+64$, with $d=2H^{14}+1$, $\Delta=H^5$ and $\mu=H^{-6}$. Fix a seed, a database $D\in\{0,1\}^{m\times m}$ and a target $i=(a^\star,b^\star)\in[m]\times\{-1,+1\}^h$. Sample
--   $$R\leftarrow\mathcal R_i,\qquad (Q,u)\leftarrow\mathrm{Query}(i,R),$$
--   and set $z=\mathrm{Hint}(D,R)$ and $\mathrm{ans}=\mathrm{Answer}(D,Q)$. Then:
--
--   1. **soundness**: $\Pr\bigl[\mathrm{Decode}(i,R,z,Q,u,\mathrm{ans})\in\{D[a^\star,b^\star],\bot\}\bigr]=1$;
--   2. **availability**: if the seed is good,
--   $$\Pr\bigl[\mathrm{Decode}(i,R,z,Q,u,\mathrm{ans})=D[a^\star,b^\star]\bigr]\ge\frac58.$$
--
--   This is property (iii) of Definition 4.1 for the majority primitive, with recovery probability $5/8$ in place of $1/2$. The correctness of Theorem 7.1 rests on it.
--
--   **Formalization Note** The probabilities average over $R\in\mathcal R_i$ the law of $(Q,u)$ under `Query`. $\bot$ is `none`. The answer is `none` (abort) or the list $\beta$ in the enumeration order of $S^+(Q)$. Soundness is stated for every seed, and availability for every good seed.
--
--   Differences from the source:
--   - encoding: probabilities over R ← R_i and (Q, u) ← Query(i, R); ⊥; ans = abort or (ok, β) → the average over R_i of the Query law; none; Option (List Bool) with β in the enumeration order of S⁺(Q) (rows in order; within a row, column labels lexicographically with coordinate 0 first and −1 before +1); reason: uniform law on a finite set; Answer and Decode use the same enumeration, so the claim's events are the same for any fixed order
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Claim 7.4.3, printed p.29 (PDF p.31); Retrieval algorithms and Eq. (23)–(24), printed pp.26–27 (PDF pp.28–29)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_Supplement_Majority

open scoped ENNReal

namespace ITPIRPreproc.MatchVec.Supplement

/-- Claim 7.4.3, printed p.29 (PDF p.31). Under the §7.2 parameters, for every seed `σ`, database
`D ∈ {0,1}^{m×m}` and target `i = (a⋆, b⋆)`, with `R ← R_i`, `(Q, u) ← Query(i, R)`,
`z = Hint(D, R)` and `ans = Answer(D, Q)`:
`Pr[Decode(i, R, z, Q, u, ans) ∈ {D[a⋆, b⋆], ⊥}] = 1`; and if the seed is good,
`Pr[Decode(i, R, z, Q, u, ans) = D[a⋆, b⋆]] ≥ 5/8`. (`⊥` is `none`.) -/
theorem claim_7_4_3 (h H : ℕ) (hh : 3 ≤ h) (hH : h + 64 ≤ H) (σ : Seed h H) (D : MDB h)
    (i : MPos h) :
    avgOver (majCompat σ i) (fun R => (majQuery σ i R).toOuterMeasure
        {p | majOutcome σ D i R p = some (D i.1 i.2) ∨ majOutcome σ D i R p = none}) = 1 ∧
    (IsGood σ →
      5 / 8 ≤ avgOver (majCompat σ i) (fun R => (majQuery σ i R).toOuterMeasure
        {p | majOutcome σ D i R p = some (D i.1 i.2)})) := by sorry

end ITPIRPreproc.MatchVec.Supplement
