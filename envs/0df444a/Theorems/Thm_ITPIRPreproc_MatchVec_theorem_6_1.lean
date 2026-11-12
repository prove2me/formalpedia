-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_theorem_6_1
-- name    : ITPIRPreproc.MatchVec.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:03.800214+00:00
-- url     : https://prove2.me/theorems/d19ad163-7b8a-488c-8890-072e9b9a7cc8
-- title:
--   Theorem 6.1 — perfectly private single-server PIR with client preprocessing: $n^{1/2+o(1)}\mathrm{poly}(\lambda)$ storage and work, $\lambda n^{o(1)}$ online and $O(\sqrt n)$ offline communication
-- statement:
--   There is a single-server information-theoretic PIR scheme with client preprocessing in the model of §3, given by one family of word-RAM programs for all database lengths $n$ and security parameters $\lambda$ (it never receives the number $T$ of retrievals), together with a function $\varepsilon(n)\to0$ and constants $C,c$, such that for every database length $n\ge1$ and integer $\lambda\ge1$:
--
--   1. the scheme has **perfect privacy**;
--   2. its **correctness error** over any $T$ retrieval protocols is at most $T\,2^{-\lambda}$;
--   3. initial preprocessing uses one database stream and client work at most $C\,n^{1+\varepsilon(n)}\lambda^c$;
--   4. each retrieval protocol uses one round trip, **online communication** at most $C\,\lambda\,n^{\varepsilon(n)}$ and **offline communication** at most $C\sqrt n$;
--   5. client storage, throughout preprocessing and every retrieval protocol, and worst-case client work and server work per retrieval protocol are at most
--   $$C\,n^{1/2+\varepsilon(n)}\,\lambda^c.$$
--
--   The server stores only the database between retrieval protocols. In the paper's notation: $n^{1+o(1)}\mathrm{poly}(\lambda)$ preprocessing work, $\lambda n^{o(1)}$ online and $O(\sqrt n)$ offline communication, and $n^{1/2+o(1)}\mathrm{poly}(\lambda)$ storage and work. For $\lambda=n^{o(1)}$ this gives $n^{o(1)}$ online communication and $n^{1/2+o(1)}$ client storage and client and server work, which matches the known lower bounds up to the $n^{o(1)}$ factors.
--
--   **Formalization Note** All bounds are worst-case over coins, reachable states and indices. Preprocessing communication $O(n)$ and server work $O(n)$ hold by construction of the model, whose preprocessing is exactly one $n$-bit stream of $D$ read by a streaming client program.
--
--   Differences from the source:
--   - reading: n^{o(1)}, poly(λ), O(·) in the bounds of (i) and (ii) → one function ε(n) → 0 and constants C, c chosen before n and λ, with bounds C·n^{1+ε(n)}·λ^c, C·λ·n^{ε(n)}, C·√n, C·n^{1/2+ε(n)}·λ^c for every n ≥ 1, λ ≥ 1; reason: paper.md Reading 1: asymptotic bounds have content only for the whole family
--   - generalization: for every n and λ there is a scheme → one scheme (five programs) for all n and λ, which receives n and λ as input; reason: a uniform family specializes to a scheme for each (n, λ); it also keeps storage from hiding in program text
--   - reading: client and server work in the RAM model; work in bit operations including random-bit generation; storage in bits → work of word-RAM programs (fair-coin instruction, word size = bit length of input length plus storage in use, each operand charged per word) and storage in bits; reason: paper.md Reading 2; a log-cost RAM would make a contiguous scan cost Θ(log n) per bit, contradicting the O(√n) server-work and offline terms
--   - encoding: a computationally unbounded adversary that chooses D and then adaptively chooses the indices → for every database D and every adversary that is a measurable function of its coin tape and the queries seen; reason: a randomized choice of D is a mixture of fixed choices; a randomized adversary's choices are events of its coins
--   - encoding: a stateful simulator Sim(1^λ, D) producing the queries without seeing the indices; the adversary's view is identically distributed → a law sim T on the first T queries, depending on n, λ, D only, with Pr[coins ∈ B ∧ (Q₁, …, Q_T) = q] = Pr[B]·sim T q for every measurable B, every q and every T; reason: the view is the adversary's coins and the queries; equality for every T is equivalent to a stateful simulator
--   - encoding: Decode(ŝtate, ans) = (y, state′), with ans_on sufficing to decode y → two deterministic programs: y from (ŝtate, ans_on) and state′ from (ŝtate, ans_on, ans_off); reason: the online/offline split of §3
--   - encoding: one database stream, O(n) preprocessing communication and server work; one round trip; the server stores only the database → Preprocess is a streaming program reading D once; one query and one answer per protocol; Answer is a deterministic function of (D, Q); O(n) preprocessing communication and server work hold by construction of the model; reason: §3 syntax
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Theorem 6.1, printed p.20 (PDF p.22)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_Model

open scoped ENNReal
open Filter Topology

namespace ITPIRPreproc.MatchVec

/-- Theorem 6.1, printed p.20 (PDF p.22). There is a single-server information-theoretic PIR scheme
with client preprocessing (one uniform family of word-RAM programs for all `n` and `λ`, which never
receives `T`), a function `ε(n) → 0` and constants `C, c`, such that for every database length
`n ≥ 1` and integer `λ ≥ 1`: the scheme has perfect privacy; its correctness error over any `T`
retrieval protocols is at most `T 2^{−λ}`; initial preprocessing (one database stream) has client
work at most `C n^{1+ε(n)} λ^c`; each retrieval protocol (one round trip) has online communication
at most `C λ n^{ε(n)}` and offline communication at most `C √n`; and client storage (throughout
preprocessing and every protocol) and worst-case client and server work per retrieval protocol
are at most `C n^{1/2+ε(n)} λ^c`. -/
theorem theorem_6_1 :
    ∃ S : Scheme, S.WellFormed ∧
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∃ (C : ℝ) (c : ℕ), ∀ n lam : ℕ, 1 ≤ n → 1 ≤ lam →
          PerfectlyPrivate S n lam ∧
          Correct S n lam (fun T => (T : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ lam) ∧
          MeetsBudget S n lam
            { preWork := C * (n : ℝ) ^ (1 + ε n) * (lam : ℝ) ^ c
              preSpace := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c
              online := C * lam * (n : ℝ) ^ (ε n)
              offline := C * Real.sqrt n
              clientWork := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c
              clientSpace := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c
              serverWork := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c } := by sorry

end ITPIRPreproc.MatchVec
