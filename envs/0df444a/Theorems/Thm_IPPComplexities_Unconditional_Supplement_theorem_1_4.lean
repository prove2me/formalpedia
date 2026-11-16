-- Prove2me | Theorems.Thm_IPPComplexities_Unconditional_Supplement_theorem_1_4
-- name    : IPPComplexities.Unconditional.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:35:24.076689+00:00
-- url     : https://prove2.me/theorems/4d7a8735-f498-4251-ad66-31537358d47f
-- title:
--   Theorem 1.4 — compressing the verifier's communication (corrected at r(n) = 0)
-- statement:
--   There are absolute positive constants $K_q,K_c,K_r$ with the following property. Let $\Pi$ be a property, $\epsilon>0$, and $V$ an IPP for $\Pi$ at proximity $\epsilon$ in which, on $n$-bit inputs, every run has at most $r(n)$ rounds, the prover sends at most $p(n)$ bits and the verifier makes at most $q(n)$ queries; nothing is assumed about the length of the verifier's own messages or its randomness. Then there is an IPP $V'$ for $\Pi$ at the same proximity such that, for every $n$,
--
--   1. $V'$ has at most $r(n)$ rounds;
--   2. $V'$ makes at most $K_q\,q(n)$ queries;
--   3. the total communication of $V'$, in both directions, is at most
--   $$K_c\bigl(p(n)+r(n)\,q(n)\,\lceil\log_2 n\rceil\bigr);$$
--   4. if $r(n)\ge1$, the randomness complexity of $V'$ is at most $K_r\,r(n)\,q(n)\,\lceil\log_2 n\rceil$;
--   5. if $V$ has perfect completeness, so does $V'$.
--
--   A round is a verifier message followed by a prover message; rounds are counted as the maximal blocks of prover bits on the public transcript, the same way for $V$ and $V'$. An IPP here is any nonuniform private-coin verifier system with $2/3$ completeness and soundness at proximity $\epsilon$.
--
--   The theorem says that the verifier gains nothing by sending messages longer than about $q(n)\log n$ bits per round, so lower bounds on two-way communication give lower bounds on the prover's communication.
--
--   **Formalization Note** $\lceil\log_2 n\rceil$ is `Nat.clog 2 n`, which is $0$ for $n\le1$. The constants are fixed before $\Pi$, $\epsilon$, $V$ and the resource functions.
--
--   Differences from the source:
--   - correction: randomness complexity O(r·q·log n) at every length → required only at lengths with r(n) ≥ 1; reason: false at r(n) = 0. Counterexample: Π = all-zero strings with the 0-round tester that makes ⌈2/ε⌉ uniformly random queries (r = p = 0). A 0-round V′ with O(0) random bits is a deterministic tester with O(q) queries, and it accepts the ε-far string whose ones avoid the positions it reads on the all-zero answers
--   - generalization: IPPs valid for every positive proximity → systems valid at the one proximity ε, with V′ valid at the same ε; reason: applying the statement at each ε, with constants independent of ε, gives the source's version for IPPs in the sense of Definition 2.1
--   - reading: an r-round IPP → at most r(n) maximal blocks of prover bits on the public transcript of every run, for V and V′ alike; reason: the paper's round is a verifier message followed by a prover message, so rounds are counted by prover messages; a prover message sent first counts as a round
--   - encoding: O(q), O(p + r·q·log n), O(r·q·log n) → absolute constants Kq, Kc, Kr fixed before Π, ε and V, with log n as ⌈log₂ n⌉; reason: makes the asymptotic quantifiers explicit; ⌈log₂ n⌉ is within a factor 2 of log₂ n for n ≥ 2
-- source:
--   Noga Amit, Oded Goldreich, STOC 2027 submission #297 (October 2026), p. 3, Theorem 1.4 (PDF p. 5); proof §7, pp. 18–27 (PDF pp. 20–29); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/297.pdf

import Definitions.Def_IPPComplexities_Unconditional_Supplement_transcripts

namespace IPPComplexities.Unconditional.Supplement

/-- Theorem 1.4, with absolute constants and the randomness clause at lengths with at
least one round (corrected: it is false at r(n) = 0). The original verifier's own
messages and randomness are unbounded. -/
theorem theorem_1_4 :
    ∃ Kq Kc Kr : ℕ, 0 < Kq ∧ 0 < Kc ∧ 0 < Kr ∧
      ∀ (L : Property) (ε : ℝ) (V : System) (r p q : ℕ → ℕ),
        ValidAt L ε V →
        (∀ n : ℕ, AtMostRounds (V n) (r n) ∧ ProverBitsBounded (V n) (p n) ∧
          QueriesBounded (V n) (q n)) →
        ∃ V' : System,
          ValidAt L ε V' ∧
          (∀ n : ℕ, AtMostRounds (V' n) (r n)) ∧
          ResourceBounds V' (fun n => Kq * q n)
            (fun n => Kc * (p n + r n * q n * Nat.clog 2 n)) ∧
          (∀ n : ℕ, 1 ≤ r n →
            RandomnessAtMost (V' n) (Kr * r n * q n * Nat.clog 2 n)) ∧
          (PerfectCompleteness L V → PerfectCompleteness L V') := by sorry

end IPPComplexities.Unconditional.Supplement
