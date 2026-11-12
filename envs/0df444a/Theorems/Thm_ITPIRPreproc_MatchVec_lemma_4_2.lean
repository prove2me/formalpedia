-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_lemma_4_2
-- name    : ITPIRPreproc.MatchVec.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:20.393111+00:00
-- url     : https://prove2.me/theorems/ca506b01-965d-4be5-912a-dbf087558e58
-- title:
--   Lemma 4.2 — from one compatible hint to full PIR: perfect privacy, error $T(7/8)^{8(\lambda+1)}$, and the compiler's costs
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $P$ be a family of One Compatible Hint PIR primitives (one for each $m$, for databases of length $n=m^2$) with an implementation. Then there is a scheme in the model of §3 (the construction of §4.2) such that, for every $m\ge8$ at which the primitive satisfies the three properties of Definition 4.1 and the efficiency requirements of §4.1 with parameters $t_{\rm basic},t_{\rm stream},\mathrm{time}(\mathsf{Query}),\mathrm{time}(\mathsf{Decode}),\mathrm{time}(\mathsf{Answer})$ and worst-case message lengths $|Q|,|\mathsf{Answer}(D,Q)|$, and for every security parameter $\lambda\ge1$, the scheme on databases of length $n=m^2$ has perfect privacy and correctness error at most
--   $$T\,(7/8)^{8(\lambda+1)}$$
--   over $T$ retrieval protocols, and, writing $\sqrt n=m$:
--
--   1. initial preprocessing sends one $n$-bit stream and has client work $O(\lambda\sqrt n\,t_{\rm basic}+\lambda n\,t_{\rm stream})$ and client storage $O(t_{\rm basic}+\lambda\sqrt n\,t_{\rm stream})$, including workspace for sampling the keys;
--   2. each retrieval protocol uses one round trip with online communication $O(\lambda(|Q|+|\mathsf{Answer}(D,Q)|)+\log n)$, offline communication $O(\sqrt n)$ and server work $O(\lambda\,\mathrm{time}(\mathsf{Answer})+\sqrt n)$;
--   3. client work per retrieval protocol and client storage are each at most
--   $$O\big(\lambda\sqrt n\,[t_{\rm basic}+t_{\rm stream}]+\lambda\,[\mathrm{time}(\mathsf{Query})+\mathrm{time}(\mathsf{Decode})]+\sqrt n\log n\big).$$
--
--   All bounds are worst-case and every $O(\cdot)$ is $C$ times the expression. The client storage bound covers the state and all temporary values of each protocol.
--
--   This is the generic compiler: any primitive meeting Definition 4.1 and §4.1 yields a full PIR scheme with client preprocessing, and Lemma 6.2 supplies one.
--
--   **Formalization Note** $\log$ is the natural logarithm. The total communication bound $O(\lambda(|Q|+|\mathsf{Answer}|)+\sqrt n)$ is the sum of the online and offline bounds.
--
--   Differences from the source:
--   - reading: the construction above has perfect privacy, error (6) and the stated costs → there exists a scheme with perfect privacy, error T(7/8)^{8(λ+1)} and the stated costs (the §4.2 construction is the witness); reason: the compiler is given in prose, and its cost claims concern an implementation by programs, which the statement can only assert to exist; every property the lemma attributes to the construction is kept
--   - generalization: one primitive for one database length n = m² → a family of primitives with one implementation and one scheme, valid at every m ≥ 8 where Definition 4.1 and §4.1 hold; reason: a single primitive at one m is such a family (placeholder elsewhere), so the statement specializes to the source
--   - generalization: the primitive's basic operations, Query and Decode receive only their arguments → they may also read a public precomputed table whose computation and size are at most E·t_stream; reason: a primitive without precomputed data has the empty table; the charge is the paper's own accounting of vector tables
--   - reading: O(·) bounds → one absolute constant C chosen before the primitive, m and λ; reason: the BRIEF's reading of the lemma's O(·) as absolute
--   - reading: client and server work in the RAM model; work in bit operations including random-bit generation; storage in bits → work of word-RAM programs (fair-coin instruction, word size = bit length of input length plus storage in use, each operand charged per word) and storage in bits; reason: paper.md Reading 2; a log-cost RAM would make a contiguous scan cost Θ(log n) per bit, contradicting the O(√n) server-work and offline terms
--   - encoding: time(A) is the worst-case bit work, including input and output processing → each time bound also bounds the length of the program's explicit arguments; outputs are charged by the machine; reason: the definition of time(·) on p.14
--   - encoding: a computationally unbounded adversary that chooses D and then adaptively chooses the indices → for every database D and every adversary that is a measurable function of its coin tape and the queries seen; reason: a randomized choice of D is a mixture of fixed choices; a randomized adversary's choices are events of its coins
--   - encoding: a stateful simulator Sim(1^λ, D) producing the queries without seeing the indices; the adversary's view is identically distributed → a law sim T on the first T queries, depending on n, λ, D only, with Pr[coins ∈ B ∧ (Q₁, …, Q_T) = q] = Pr[B]·sim T q for every measurable B, every q and every T; reason: the view is the adversary's coins and the queries; equality for every T is equivalent to a stateful simulator
--   - encoding: Decode(ŝtate, ans) = (y, state′), with ans_on sufficing to decode y → two deterministic programs: y from (ŝtate, ans_on) and state′ from (ŝtate, ans_on, ans_off); reason: the online/offline split of §3
--   - encoding: initial preprocessing sends one n-bit stream, uses O(n) server work; one round trip; the server retains only D → the model's preprocessing is the n-bit stream of D read by a streaming client program, with no server computation; one query and one answer per protocol; Answer is a deterministic function of (D, Q); reason: §3 syntax; these clauses hold by construction of the model
--   - encoding: total communication = O(λ(|Q| + |Answer(D, Q)|) + √n) → not stated separately; reason: it is the sum of the online and offline bounds, since log n ≤ √n
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Lemma 4.2, printed p.14 (PDF p.16), Eq. (5) and (6); §4 standing assumption n = m², m ≥ 8, printed p.11 (PDF p.13)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_Model
import Definitions.Def_ITPIRPreproc_MatchVec_Efficiency

open scoped ENNReal

namespace ITPIRPreproc.MatchVec

open WordRAM

/-- Lemma 4.2, printed p.14 (PDF p.16). There is an absolute constant `C` such that for every
family of primitives with an implementation, there is a scheme (the compiler of §4.2) with the
following property: whenever at size `m ≥ 8` (`n = m²`, `√n = m`) the primitive satisfies
Definition 4.1 and the efficiency requirements of §4.1 with parameters `t_basic`, `t_stream`,
`time(Query)`, `time(Decode)`, `time(Answer)`, `|Q|`, `|Answer(D, Q)|`, then for every `λ ≥ 1` the
scheme has perfect privacy, correctness error at most `T (7/8)^{8(λ+1)}` over `T` retrieval
protocols, and the stated worst-case costs: preprocessing client work
`O(λ√n t_basic + λ n t_stream)` and storage `O(t_basic + λ√n t_stream)`; per retrieval protocol
online communication `O(λ(|Q| + |Answer|) + log n)`, offline communication `O(√n)`, server work
`O(λ time(Answer) + √n)`, client work and client storage
`O(λ√n [t_basic + t_stream] + λ[time(Query) + time(Decode)] + √n log n)`. -/
theorem lemma_4_2 :
    ∃ C : ℝ, ∀ (P : ∀ m : ℕ, OCHP (m * m)) (I : OCHPImpl P),
      ∃ S : Scheme, S.WellFormed ∧
        ∀ (m : ℕ) (tB tS tQ tD tA : ℝ) (qLen aLen : ℕ), 8 ≤ m →
          (P m).IsOneCompatibleHint m → I.Efficient m tB tS tQ tD tA qLen aLen →
          ∀ lam : ℕ, 1 ≤ lam →
            PerfectlyPrivate S (m * m) lam ∧
            Correct S (m * m) lam (fun T => (T : ℝ≥0∞) * (7 / 8 : ℝ≥0∞) ^ (8 * (lam + 1))) ∧
            MeetsBudget S (m * m) lam
              { preWork := C * (lam * m * tB + lam * (m * m) * tS)
                preSpace := C * (tB + lam * m * tS)
                online := C * (lam * (qLen + aLen) + Real.log (m * m))
                offline := C * m
                clientWork := C * (lam * m * (tB + tS) + lam * (tQ + tD) + m * Real.log (m * m))
                clientSpace := C * (lam * m * (tB + tS) + lam * (tQ + tD) + m * Real.log (m * m))
                serverWork := C * (lam * tA + m) } := by sorry

end ITPIRPreproc.MatchVec
