-- Prove2me | Theorems.Thm_IPPComplexities_Unconditional_Supplement_theorem_3_2
-- name    : IPPComplexities.Unconditional.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:36:18.023191+00:00
-- url     : https://prove2.me/theorems/ab72283b-ed17-4812-b8ef-ab531352b107
-- title:
--   Theorem 3.2 — circuit size of verification strategies for IPPs
-- statement:
--   There are absolute positive integers $K_q,K_c,A,D$ with the following property. Let $\Pi$ be a property, $\epsilon>0$, and $V$ an IPP for $\Pi$ at proximity $\epsilon$ with worst-case query complexity $q(n)$ and two-way communication complexity $c(n)$. Then there is a family $(C_n)_{n\in\mathbb N}$ of well-formed probabilistic circuits such that the verifiers $V'_n$ implemented by the $C_n$ form an IPP for $\Pi$ at the same proximity and, for every $n$,
--
--   $$Q_{V'}(n)\le K_q\,q(n),\qquad C_{V'}(n)\le K_c\,c(n),\qquad |C_n|\le B_{A,D}(n,q(n)+c(n)),$$
--
--   where $B_{A,D}(n,t)=(A\max\{n,2\})^{D t}$ for $t>0$ and $B_{A,D}(n,0)=A$, i.e. $|C_n|=\mathrm{poly}(n)^{O(q(n)+c(n))}$.
--
--   An IPP here is any nonuniform private-coin verifier system with $2/3$ completeness and soundness, with no restriction on its computational complexity. A probabilistic circuit implements a verifier by being evaluated, with one random pad fixed for the whole run, on the view so far and outputting the next action (halt, query, send, receive); its size counts its random-input wires, its view-input wires and its gates. The family may be nonuniform in $n$.
--
--   Theorem 3.2 turns the query and communication complexities of an IPP into a bound on the circuit size of a verifier strategy, which is how the conditional lower bounds (Theorem 1.2 and Section 6) are derived.
--
--   **Formalization Note** The bound $B_{A,D}$ is the published `descriptionBound`, the same scale as Lemma 3.1. The query and communication bounds are kept separate. The circuit verifier's messages alternate strictly between the parties.
--
--   Differences from the source:
--   - generalization: IPPs valid for every positive proximity → systems valid at the one proximity ε, with the new system valid at the same ε; reason: applying the statement at each ε, with constants independent of ε, gives the source's version for IPPs in the sense of Definition 2.1
--   - generalization: an IPP whose verification strategy can be implemented by probabilistic circuits → the new IPP is literally the verifier implemented by the circuits, with strictly alternating messages; reason: a stronger conclusion, which gives the source's
--   - encoding: O(q), O(c) and poly(n)^{O(c(n)+q(n))}-sized circuits → absolute positive Kq, Kc, A, D and the bound B_{A,D}, with a constant at q+c = 0 and circuit size counting input wires and gates; reason: makes the asymptotic quantifiers explicit; the constant at zero resources and the input wires are absorbed by the polynomial scale
-- source:
--   Noga Amit, Oded Goldreich, STOC 2027 submission #297 (October 2026), p. 9, Theorem 3.2 (PDF p. 11); proof as for Lemma 3.1, pp. 7–8 (PDF pp. 9–10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/297.pdf

import Definitions.Def_IPPComplexities_Unconditional_validity
import Definitions.Def_IPPComplexities_Unconditional_encoding
import Definitions.Def_IPPComplexities_Unconditional_Supplement_circuitVerifier

namespace IPPComplexities.Unconditional.Supplement

/-- Theorem 3.2, with absolute separate resource factors: every valid IPP has a
valid IPP whose length-n verifier is implemented by a well-formed probabilistic
circuit of size poly(n)^{O(q(n)+c(n))}. The family is nonuniform in n. -/
theorem theorem_3_2 :
    ∃ Kq Kc A D : ℕ, 0 < Kq ∧ 0 < Kc ∧ 0 < A ∧ 0 < D ∧
      ∀ (L : Property) (ε : ℝ) (V : System) (q c : ℕ → ℕ),
        ValidAt L ε V → ResourceBounds V q c →
        ∃ C : ℕ → ProbCircuit,
          (∀ n : ℕ, (C n).WF) ∧
          ValidAt L ε (fun n => circuitVerifier n (C n)) ∧
          ResourceBounds (fun n => circuitVerifier n (C n))
            (fun n => Kq * q n) (fun n => Kc * c n) ∧
          ∀ n : ℕ, (C n).size ≤ descriptionBound A D n (q n + c n) := by sorry

end IPPComplexities.Unconditional.Supplement
