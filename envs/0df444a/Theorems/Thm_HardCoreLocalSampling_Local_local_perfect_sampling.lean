-- Prove2me | Theorems.Thm_HardCoreLocalSampling_Local_local_perfect_sampling
-- name    : HardCoreLocalSampling.Local.local_perfect_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:51.50675+00:00
-- url     : https://prove2.me/theorems/db55a5c2-9036-489f-8181-12579cbc4155
-- title:
--   Theorem 1 — Local perfect sampling
-- statement:
--   Fix an integer $\Delta\ge3$ and a positive rational $\lambda<\lambda_c(\Delta)=(\Delta-1)^{\Delta-1}/(\Delta-2)^\Delta$. There is an algorithm which, given a vertex of any finite simple undirected graph of maximum degree at most $\Delta$ and any feasible hard-core pinning, returns a bit with exactly its conditional unoccupied marginal:
--
--   $$
--   \Pr[\text{output}=1]=\mu_\xi(v\notin I).
--   $$
--
--   The expected number of graph and pinning queries, label/address word operations, and remaining bit operations is $O_{\Delta,\lambda}(1)$, uniformly over the graph, vertex, and pinning. If label and address operations are charged at their bit cost, the non-oracle expected running time is $O_{\Delta,\lambda}(\operatorname{polylog}(n+2))$.
--
--   The algorithm is a finite program of the machine language: it has only adjacency-list and pin oracles and fair bits, and no real arithmetic. Parameter-dependent preprocessing is an effective map from $(\Delta,\lambda)$ to code. Output law and costs are derived from one run, and a nonterminating run has infinite cost. Constants are chosen before the input.
--
--   Differences from the source:
--   - encoding: an algorithm in the informally described word and bit cost model → a finite program of the Machine language; reason: a concrete instruction set of that model; every such program is an algorithm in the source's model, and restricting address arithmetic to increment, decrement and paid conversion only charges more than the source does
--   - reading: parameter-dependent preprocessing is finite and effective → one Computable map sends Δ and the numerator and denominator of λ to finite code; reason: uniform computability is the stronger reading; for a fixed pair the existence of finite code would make effectivity trivial
--   - encoding: labels of O(log(n+2)) bits → vertices are natural-number labels of at most κ⌈log₂(n+2)⌉ bits, with the word bound chosen before κ and the bit bound after; reason: κ is the implied constant, and the word bound does not see label length
--   - encoding: non-oracle running time with label and address operations at bit cost → the bit account charges an oracle query for its operand and answer lengths and not for the oracle's internal work; reason: this is the non-oracle cost of handling queries, and it is at most polylogarithmic per query in the source's analysis
--   - encoding: expected cost of an algorithm that terminates almost surely → almost-sure termination and measurability of work are stated explicitly, and work is infinite on a nonterminating tape; reason: the source's bit and its cost are random variables with these properties
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, Theorem 1, printed p.2 (PDF p.3); computational model §2, printed p.2 (PDF p.3); Appendix A, printed p.13 (PDF p.14)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Params
import Definitions.Def_HardCoreLocalSampling_Local_Instance

namespace HardCoreLocalSampling.Local

/-- Thomas Chen, STOC 2027 submission #462, Theorem 1 (Local perfect sampling), printed p.2
(PDF p.3). Effective preprocessing computes finite code from `Δ` and `λ`. For each fixed `Δ`, `λ`,
the program's output on every graph of maximum degree at most `Δ`, every feasible pinning and every
vertex has exactly the conditional unoccupied law; it halts almost surely; its expected intrinsic
work is at most `Cw`, chosen before the input and before the label-length constant `κ`; and with
label and address operations charged at their bit length, its expected non-oracle cost is
`O_{Δ,λ}(polylog(n+2))`. Work is measurable and infinite on nonterminating tapes. -/
theorem local_perfect_sampling :
    ∃ code : ℕ × ℕ × ℕ → List InstrCode, Computable code ∧
      ∀ (Delta : ℕ) (lam : ℚ), Standing Delta lam →
        let P := decodeProgram (code (Delta, lam.num.toNat, lam.den))
        ∃ Cw : NNReal, ∀ κ : ℕ, ∃ (Cb : NNReal) (e : ℕ),
          ∀ (I : LocalInstance), ValidInput I Delta → I.LabelsBounded κ → ∀ v : I.vertices,
            ExactUnoccupiedBit P I lam v ∧
            Measurable (fun ω => wordWork P I.oracle ω noExt (queryConfig v)) ∧
            Measurable (fun ω => bitWork P I.oracle ω noExt (queryConfig v)) ∧
            ∫⁻ ω, wordWork P I.oracle ω noExt (queryConfig v) ∂fairMeasure ≤ Cw ∧
            ∫⁻ ω, bitWork P I.oracle ω noExt (queryConfig v) ∂fairMeasure ≤
              polylogBound Cb e I.n := by sorry

end HardCoreLocalSampling.Local
