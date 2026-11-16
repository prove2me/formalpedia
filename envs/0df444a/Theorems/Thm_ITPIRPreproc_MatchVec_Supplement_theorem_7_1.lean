-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_Supplement_theorem_7_1
-- name    : ITPIRPreproc.MatchVec.Supplement.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:53:36.053826+00:00
-- url     : https://prove2.me/theorems/1b4e6c8b-0194-4582-9568-aa963fe75f7f
-- title:
--   Theorem 7.1 — majority construction: perfectly private PIR with $\sqrt n\,\mathrm{poly}(\log n,\lambda)$ storage and work, $O(\lambda\sqrt n)+\mathrm{poly}(\log n,\lambda)$ online communication
-- statement:
--   There is a single-server information-theoretic PIR scheme with client preprocessing in the model of §3. It is given by one family of word-RAM programs for all database lengths $n$ and security parameters $\lambda$, and it never receives the number $T$ of retrievals. There are constants $C,c$ such that, writing $\ell(n)=\lfloor\log_2 n\rfloor+1$, for every database length $n\ge1$ and integer $\lambda\ge1$:
--
--   1. the scheme has **perfect privacy**;
--   2. its **correctness error** over any $T$ retrieval protocols is at most $T\,2^{-\lambda}$;
--   3. initial preprocessing uses one database stream and client work at most $C\,n\,\ell(n)^c\lambda^c$;
--   4. each retrieval protocol uses one round trip, **online communication** at most $C\bigl(\lambda\sqrt n+\ell(n)^c\lambda^c\bigr)$ and **offline communication** at most $C\sqrt n$;
--   5. client storage, throughout preprocessing and every retrieval protocol, and worst-case client work and server work per retrieval protocol are at most
--   $$C\,\sqrt n\,\ell(n)^c\,\lambda^c.$$
--
--   The server stores only the database between retrieval protocols. In the paper's notation, preprocessing takes $n\,\mathrm{poly}(\log n,\lambda)$ client work, online and total communication are $O(\lambda\sqrt n)+\mathrm{poly}(\log n,\lambda)$, offline communication is $O(\sqrt n)$, and storage and work are $\sqrt n\,\mathrm{poly}(\log n,\lambda)$. This is a companion theorem to the mission's goal, Theorem 6.1. It trades the $n^{o(1)}$ factors for polylogarithmic ones and pays with online communication $\tilde O(\sqrt n)$ in place of $\lambda n^{o(1)}$. It is not used in the proof of Theorem 6.1.
--
--   **Formalization Note** All bounds are worst-case over coins, reachable states and indices. Preprocessing communication $O(n)$ and server work $O(n)$ hold by construction of the model, whose preprocessing is exactly one $n$-bit stream of $D$ read by a streaming client program. Total communication is online plus offline, so its bound follows from item 4. There is no $\varepsilon(n)$, because no bound has an $n^{o(1)}$ factor.
--
--   Differences from the source:
--   - reading: poly(log n, λ) and O(·) in the bounds of (i) and (ii) → constants C, c chosen before n and λ, with bounds C·n·ℓ(n)^c·λ^c, C·(λ√n + ℓ(n)^c·λ^c), C·√n, C·√n·ℓ(n)^c·λ^c for every n ≥ 1, λ ≥ 1, where ℓ(n) = ⌊log₂ n⌋ + 1; reason: asymptotic bounds have content only for the whole family (paper.md Reading 1, adapted to polylogarithmic factors); ℓ(n) ≥ 1 at n = 1
--   - generalization: for every n and λ there is a scheme → one scheme (five programs) for all n and λ, which receives n and λ as input; reason: a uniform family specializes to a scheme for each (n, λ); it also keeps storage from hiding in program text
--   - reading: client and server work in the RAM model; work in bit operations including random-bit generation; storage in bits → work of word-RAM programs (fair-coin instruction, word size = bit length of input length plus storage in use, each operand charged per word) and storage in bits; reason: paper.md Reading 2; the model is the published one of the base mission; the work bounds carry a poly(log n) slack, and communication is counted in bits independently of the cost model
--   - encoding: a computationally unbounded adversary that chooses D and then adaptively chooses the indices → for every database D and every adversary that is a measurable function of its coin tape and the queries seen; reason: a randomized choice of D is a mixture of fixed choices; a randomized adversary's choices are events of its coins
--   - encoding: a stateful simulator Sim(1^λ, D) producing the queries without seeing the indices; the adversary's view is identically distributed → a law sim T on the first T queries, depending on n, λ, D only, with Pr[coins ∈ B ∧ (Q₁, …, Q_T) = q] = Pr[B]·sim T q for every measurable B, every q and every T; reason: the view is the adversary's coins and the queries; equality for every T is equivalent to a stateful simulator
--   - encoding: Decode(ŝtate, ans) = (y, state′), with ans_on sufficing to decode y → two deterministic programs: y from (ŝtate, ans_on) and state′ from (ŝtate, ans_on, ans_off); reason: the online/offline split of §3
--   - encoding: one database stream, O(n) preprocessing communication and server work; one round trip; the server stores only the database; client storage counts state and temporaries, and the same storage suffices for the streaming preprocessing → Preprocess is a streaming program reading D once; one query and one answer per protocol; Answer is a deterministic function of (D, Q); preprocessing storage has the per-retrieval storage budget; O(n) preprocessing communication and server work hold by construction of the model; reason: §3 syntax and efficiency conventions
--   - encoding: O(λ√n) + poly(log n, λ) online and total communication → online |Q| + |ans_on| ≤ C·(λ√n + ℓ(n)^c·λ^c) and offline |ans_off| ≤ C·√n; reason: total = online + offline, so the total bound follows with constant 2C
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Theorem 7.1, printed p.24 (PDF p.26); model §3, printed pp.9–10 (PDF pp.11–12)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_Model

open scoped ENNReal

namespace ITPIRPreproc.MatchVec.Supplement

/-- Theorem 7.1, printed p.24 (PDF p.26). There is a single-server information-theoretic PIR
scheme with client preprocessing (one uniform family of word-RAM programs for all `n` and `λ`,
which never receives `T`) and constants `C, c` such that, writing `ℓ(n) = ⌊log₂ n⌋ + 1`, for every
database length `n ≥ 1` and integer `λ ≥ 1`: the scheme has perfect privacy; its correctness error
over any `T` retrieval protocols is at most `T 2^{−λ}`; initial preprocessing (one database stream)
has client work at most `C n ℓ(n)^c λ^c`; each retrieval protocol (one round trip) has online
communication at most `C (λ √n + ℓ(n)^c λ^c)` and offline communication at most `C √n`; and client
storage (throughout preprocessing and every protocol) and worst-case client and server work per
retrieval protocol are at most `C √n ℓ(n)^c λ^c`. -/
theorem theorem_7_1 :
    ∃ S : Scheme, S.WellFormed ∧
      ∃ (C : ℝ) (c : ℕ), ∀ n lam : ℕ, 1 ≤ n → 1 ≤ lam →
        PerfectlyPrivate S n lam ∧
        Correct S n lam (fun T => (T : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ lam) ∧
        MeetsBudget S n lam
          { preWork := C * n * ((Nat.log 2 n : ℝ) + 1) ^ c * (lam : ℝ) ^ c
            preSpace := C * Real.sqrt n * ((Nat.log 2 n : ℝ) + 1) ^ c * (lam : ℝ) ^ c
            online := C * (lam * Real.sqrt n + ((Nat.log 2 n : ℝ) + 1) ^ c * (lam : ℝ) ^ c)
            offline := C * Real.sqrt n
            clientWork := C * Real.sqrt n * ((Nat.log 2 n : ℝ) + 1) ^ c * (lam : ℝ) ^ c
            clientSpace := C * Real.sqrt n * ((Nat.log 2 n : ℝ) + 1) ^ c * (lam : ℝ) ^ c
            serverWork := C * Real.sqrt n * ((Nat.log 2 n : ℝ) + 1) ^ c * (lam : ℝ) ^ c } := by sorry

end ITPIRPreproc.MatchVec.Supplement
