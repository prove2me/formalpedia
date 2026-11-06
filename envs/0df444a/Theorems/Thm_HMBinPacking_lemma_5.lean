-- Prove2me | Theorems.Thm_HMBinPacking_lemma_5
-- name    : HMBinPacking.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:01:46.771519+00:00
-- url     : https://prove2.me/theorems/5f66cb9c-42fb-40c7-8b0f-0f1d95c08351
-- title:
--   Lemma 5 — integer feasibility over a bounded closed convex set with $2^{O(n^3)}\sigma^{O(1)}$ separation calls
-- statement:
--   Let $n\ge1$, let $T\ge1$ be a given rational number, let $Q\subseteq[-T,T]^n$ be a closed convex set (possibly empty), and let $\sigma\ge n+\mathrm{enc}(T)$ be a given integer. Suppose a strong separation oracle for $Q$ answers every query $y$ with an answer of encoding length at most $(\sigma+\ell)^{e}$, where $\ell$ is the encoding length of $y$ and $e$ is a fixed exponent.
--
--   Then, for a constant $c$ depending only on $e$, one deterministic oracle algorithm, given $(n,T,\sigma)$ and the oracle, either finds a point of $Q\cap\mathbb Z^n$ or certifies
--   $$
--   Q\cap\mathbb Z^n=\emptyset,
--   $$
--   using at most $2^{c n^3}\sigma^{c}$ calls to the oracle and additional bit operations, with every query of length at most $2^{c n^3}\sigma^{c}$.
--
--   The algorithm is the same for every $Q$ and every oracle answering separation for $Q$; it is not allowed to depend on $Q$. This is the cited integer programming result ([Dad12, DV12]) that the proof of Theorem 1 applies to $K$.
--
--   Differences from the source:
--   - encoding: an algorithm using calls to strong separation [optimization] and additional bit operations, with query lengths bounded → OracleMachine: a Mathlib FinTM2 with a Boolean query stack and labels ask/resume; oracle O : List Bool → List Bool; every step, including each call, costs 1 (ORunsWithin); query length = length of the query stack at each call; reason: the paper counts calls and bit operations together; one machine is fixed before the set and the oracle, so it cannot depend on Q
--   - encoding: enc(q): total binary encoding length of a rational number or vector, including numerators and denominators; ℓ the encoding length of the query → lengths of the published codes encodeRat q and encVec v; reason: the codes are binary with numerator and denominator, so the lengths agree with the paper's up to constant factors, which polynomial bounds absorb
--   - encoding: (·)^{O(1)} and 2^{O(d³)} bounds → explicit constants: ∃ c before every instance with (·)^c and 2^(c·d^3); for a hypothesis with (·)^{O(1)}, ∀ e first; reason: the O-notation read as one constant uniform over all inputs
--   - encoding: the found point or the certificate of emptiness → output word true :: encodeIntVec x with x ∈ Q ∩ ℤ^n, or [false] with Q ∩ ℤ^n = ∅; reason: the algorithm's answer written as a binary word
--   - encoding: σ a given integer with σ ≥ n + enc(T) → σ : ℕ; reason: σ ≥ n + enc(T) ≥ 1 forces σ to be positive
--   - encoding: a strong separation oracle over Q → any O : List Bool → List Bool with IsSepAnswer Q y (O (encVec y)) for every rational y; words that do not encode a vector are answered arbitrarily; reason: the oracle as a function on binary words; the machine is correct for every such oracle
--   - reading: u⊤x ≤ α < u⊤y for every x ∈ Q, which for an empty Q, read literally, would not constrain α < u⊤y → IsSepAnswer requires α < u⊤y in every case, also for Q = ∅; reason: the answer has to separate y; the paper's own answer for an empty set, 0⊤x ≤ −1 in the proof of Lemma 7, satisfies it
--   - encoding: the given n, T and σ → input word encodeNat n ++ encodeRat T ++ encodeNat σ; reason: binary word
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, Lemma 5 ([Dad12, DV12]), p.5

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_HMBinPacking_Encoding
import Definitions.Def_HMBinPacking_Casts
import Definitions.Def_HMBinPacking_Oracles
import Definitions.Def_HMBinPacking_OracleMachine
open ExponomialAssortment.FPTAS (encodeNat encodeRat)

namespace HMBinPacking

/-- **Lemma 5: integer feasibility over a bounded closed convex set from strong separation.**
Koana, Kumabe, arXiv:2609.16923v2, Lemma 5, p.5: "Lemma 5 ([Dad12, DV12]). Let Q ⊆ [−T, T]^n be a
closed convex set, possibly empty, where n ≥ 1 and the rational number T ≥ 1 is given. Let
σ ≥ n + enc(T) be a given integer. Suppose strong separation over Q returns inequalities of encoding
length (σ + ℓ)^{O(1)}. One can deterministically find a point of Q ∩ Z^n or certify that this
intersection is empty using at most 2^{O(n³)} σ^{O(1)} calls to strong separation and additional bit
operations, with query lengths at most 2^{O(n³)} σ^{O(1)}."

For every exponent `e` there are a constant `c` and one oracle machine such that: for every `n ≥ 1`,
rational `T ≥ 1`, integer `σ ≥ n + enc(T)`, closed convex `Q ⊆ [−T, T]^n` and every oracle `O` that
answers strong separation over `Q` with answers of length at most `(σ + ℓ)^e`, the machine with
oracle `O` on input `(n, T, σ)` halts within `2^(c·n³)·σ^c` steps, with queries of length at most
`2^(c·n³)·σ^c`, and outputs either `true` followed by the code of a point of `Q ∩ ℤ^n`, or `[false]`
when `Q ∩ ℤ^n = ∅`.

**Formalization Note.** The oracle machine and its unit-cost step (each call and each machine step
costs 1) are `OracleMachine` and `ORunsWithin`. The machine exists before `n`, `T`, `σ`, `Q` and `O`,
so it cannot depend on `Q`. The exponent `e` of the hypothesis is quantified first, and `c` after it.
`Q` is not assumed nonempty, rational or full-dimensional. `σ` is a natural number since
`σ ≥ n + enc(T) ≥ 1`. Words that are not codes of rational vectors may be answered arbitrarily. -/
theorem lemma_5 :
    ∀ e : ℕ, ∃ (c : ℕ) (OM : OracleMachine),
      ∀ (n : ℕ), 1 ≤ n → ∀ (T : ℚ), 1 ≤ T → ∀ (σ : ℕ), n + enc T ≤ σ →
      ∀ Q : Set (Fin n → ℝ), IsClosed Q → Convex ℝ Q → (∀ x ∈ Q, ∀ i, |x i| ≤ (T : ℝ)) →
      ∀ O : List Bool → List Bool,
        (∀ y : Fin n → ℚ, IsSepAnswer Q y (O (encVec y)) ∧
          (O (encVec y)).length ≤ (σ + (encVec y).length) ^ e) →
        ∃ w : List Bool,
          ORunsWithin OM O (encodeNat n ++ encodeRat T ++ encodeNat σ) w
            (2 ^ (c * n ^ 3) * σ ^ c) (2 ^ (c * n ^ 3) * σ ^ c) ∧
          ((∃ x : Fin n → ℤ, w = true :: encodeIntVec x ∧ zCast x ∈ Q) ∨
            (w = [false] ∧ ∀ x : Fin n → ℤ, zCast x ∉ Q)) := by sorry

end HMBinPacking
