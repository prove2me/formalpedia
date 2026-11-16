-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_Supplement_lemma_7_2
-- name    : ITPIRPreproc.MatchVec.Supplement.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:50:44.359371+00:00
-- url     : https://prove2.me/theorems/358dd255-4a7e-41ae-b9f5-6a67470a4bd4
-- title:
--   Lemma 7.2 — majority signs of two nearly orthogonal sign vectors are nearly uncorrelated
-- statement:
--   Let $d$ be odd and let $v,v'\in\{-1,+1\}^d$ be sign vectors whose integer inner product satisfies $|\langle v,v'\rangle|\le\mu d$, where $0\le\mu\le\tfrac12$. Let $r$ be uniform on $\{-1,+1\}^d$. Then for any $b,b'\in\{-1,+1\}$,
--   $$\Pr\bigl[\operatorname{sgn}\langle r,v\rangle=b,\ \operatorname{sgn}\langle r,v'\rangle=b'\bigr]\le\frac14+8\sqrt\mu+\frac4{\sqrt d}.$$
--
--   The two majority signs of a random sign vector with respect to nearly orthogonal directions thus behave almost like independent fair signs. This drives the overlap bound $\Pr_{R\leftarrow\mathcal R_i}[j\in S(R)]\le 2/m$ of Claim 7.4.1.
--
--   **Formalization Note** The probability is the number of sign vectors $r$ with $0<b\langle r,v\rangle$ and $0<b'\langle r,v'\rangle$ divided by $2^d$. Since $b=\pm1$, $\operatorname{sgn}x=b$ holds exactly when $0<bx$. The lemma holds for every odd $d$ and every $\mu\in[0,1/2]$, not only for the parameters (19), and the constants $1/4$, $8$, $4$ are those of the paper.
--
--   Differences from the source:
--   - encoding: Pr over uniform r ∈ {−1,+1}^d of sgn⟨r,v⟩ = b and sgn⟨r,v′⟩ = b′ → the number of r : Fin d → ℤˣ with 0 < b⟨r,v⟩ and 0 < b′⟨r,v′⟩, divided by 2^d; reason: b = ±1, so sgn x = b iff 0 < b x; uniform law on a finite set; same probability
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Lemma 7.2, printed p.25 (PDF p.27)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_Supplement_Majority

namespace ITPIRPreproc.MatchVec.Supplement

/-- Lemma 7.2, printed p.25 (PDF p.27). Let `d` be odd and `v, v′ ∈ {−1,+1}^d` with
`|⟨v, v′⟩| ≤ μ d`, `0 ≤ μ ≤ 1/2`. For uniform `r ∈ {−1,+1}^d` and any `b, b′ ∈ {−1,+1}`,
`Pr[sgn⟨r, v⟩ = b, sgn⟨r, v′⟩ = b′] ≤ 1/4 + 8√μ + 4/√d`. Since `b = ±1`, the event
`sgn⟨r, v⟩ = b` is `0 < b⟨r, v⟩`; the probability is the fraction of the `2^d` sign vectors. -/
theorem lemma_7_2 (d : ℕ) (hd : Odd d) (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1 / 2)
    (v v' : Fin d → ℤˣ) (hvv : |((ip v v' : ℤ) : ℝ)| ≤ μ * d) (b b' : ℤˣ) :
    (((Finset.univ.filter fun r : Fin d → ℤˣ =>
        0 < (b : ℤ) * ip r v ∧ 0 < (b' : ℤ) * ip r v').card : ℝ) / (2 : ℝ) ^ d) ≤
      1 / 4 + 8 * Real.sqrt μ + 4 / Real.sqrt d := by sorry

end ITPIRPreproc.MatchVec.Supplement
