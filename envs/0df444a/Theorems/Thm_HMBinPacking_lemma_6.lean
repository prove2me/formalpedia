-- Prove2me | Theorems.Thm_HMBinPacking_lemma_6
-- name    : HMBinPacking.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:02:09.860542+00:00
-- url     : https://prove2.me/theorems/29321f6a-099d-4e60-9493-8d4f03bb9569
-- title:
--   Lemma 6 — strong separation from strong optimization over a rational polytope ([GLS88], Thm 6.4.9)
-- statement:
--   Let $Q\subseteq\mathbb R^n$ be a nonempty rational polytope whose vertices have encoding length at most $v$. Suppose a strong optimization oracle for $Q$ answers every objective $u\in\mathbb Q^n$ with a point of encoding length polynomial in $n+v+\mathrm{enc}(u)$ (at most $(n+v+\mathrm{enc}(u)+1)^{e}$ for a fixed exponent $e$).
--
--   Then, for a constant $c$ depending only on $e$, one oracle algorithm, given $(n,v,y)$ for a query $y\in\mathbb Q^n$ of encoding length $\ell$, returns a strong separation answer for $y$ over $Q$, using at most
--   $$
--   (n+v+\ell+1)^{c}
--   $$
--   calls to the optimization oracle and additional bit operations, with every query and the output of length at most $(n+v+\ell+1)^{c}$.
--
--   The algorithm is the same for every polytope and every oracle; $Q$ need not be full-dimensional. Lemma 7 applies it to $P_r$.
--
--   Differences from the source:
--   - encoding: an algorithm using calls to strong separation [optimization] and additional bit operations, with query lengths bounded → OracleMachine: a Mathlib FinTM2 with a Boolean query stack and labels ask/resume; oracle O : List Bool → List Bool; every step, including each call, costs 1 (ORunsWithin); query length = length of the query stack at each call; reason: the paper counts calls and bit operations together; one machine is fixed before the set and the oracle, so it cannot depend on Q
--   - encoding: enc(q): total binary encoding length of a rational number or vector, including numerators and denominators; ℓ the encoding length of the query → lengths of the published codes encodeRat q and encVec v; reason: the codes are binary with numerator and denominator, so the lengths agree with the paper's up to constant factors, which polynomial bounds absorb
--   - encoding: (·)^{O(1)} and 2^{O(d³)} bounds → explicit constants: ∃ c before every instance with (·)^c and 2^(c·d^3); for a hypothesis with (·)^{O(1)}, ∀ e first; reason: the O-notation read as one constant uniform over all inputs
--   - encoding: strong separation returns u ∈ Q^n and α ∈ Q, or certifies membership → IsSepAnswer: the output word is [true] (with y ∈ Q) or false :: encVec u ++ encodeRat α (with u⊤x ≤ α on Q and α < u⊤y); reason: the oracle's answer written as a binary word; the two cases are exclusive
--   - encoding: nonempty rational polytope with vertex encoding length at most v → Q = convexHull of a finite nonempty set V ⊆ ℚ^n, every extreme point of Q having a rational code of length ≤ v; reason: a rational polytope is the convex hull of its finitely many rational vertices, and its vertices are its extreme points
--   - encoding: (n + v + enc(u))^{O(1)} and (n + v + ℓ)^{O(1)} → (n + v + enc(u) + 1)^e and (n + v + ℓ + 1)^c; reason: at n = v = ℓ = 0 the printed form is 0 and would allow no step and no output; for arguments ≥ 2 the two classes of polynomial bounds coincide, and the only input with argument 1 is n = 0, v = 1, where Q is a point
--   - encoding: n, v and the query y → input word encodeNat n ++ encodeNat v ++ encVec y; reason: binary word
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, Lemma 6 ([GLS88], Theorem 6.4.9), p.5

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_HMBinPacking_Encoding
import Definitions.Def_HMBinPacking_Casts
import Definitions.Def_HMBinPacking_Oracles
import Definitions.Def_HMBinPacking_OracleMachine
open ExponomialAssortment.FPTAS (encodeNat)

namespace HMBinPacking

/-- **Lemma 6: strong separation from strong optimization over a rational polytope.**
Koana, Kumabe, arXiv:2609.16923v2, Lemma 6, p.5: "Lemma 6 ([GLS88], Theorem 6.4.9). Let Q ⊆ R^n be
a nonempty rational polytope with vertex encoding length at most v. Suppose strong optimization over
Q, on input u ∈ Q^n, returns a point of encoding length (n + v + enc(u))^{O(1)}. Strong separation
over Q can be implemented using (n + v + ℓ)^{O(1)} calls to strong optimization and additional bit
operations, with query and output lengths (n + v + ℓ)^{O(1)}."

For every exponent `e` there are a constant `c` and one oracle machine such that: for every `n`, `v`,
every nonempty rational polytope `Q = conv(V) ⊆ ℝ^n` (`V ⊆ ℚ^n` finite) whose vertices have
encoding length at most `v`, every oracle `O` answering strong optimization over `Q` with answers of
length at most `(n + v + enc(u) + 1)^e`, and every query `y ∈ ℚ^n`, the machine with oracle `O` on
input `(n, v, y)` halts within `(n + v + ℓ + 1)^c` steps, with queries of length at most
`(n + v + ℓ + 1)^c`, and outputs a strong separation answer for `y` of length at most
`(n + v + ℓ + 1)^c`, where `ℓ` is the encoding length of `y`.

**Formalization Note.** A rational polytope is the convex hull of a finite nonempty set of rational
points; its vertices are its extreme points, each of which has a rational code of length at most
`v`. `Q` need not be full-dimensional. The machine exists before `n`, `v`, `Q`, `O` and `y`; `e` is
quantified first. Each step, including each oracle call, costs 1 (`ORunsWithin`). The printed
`(n + v + ℓ)^{O(1)}` is written `(n + v + ℓ + 1)^c`: at `n = v = ℓ = 0` the printed form would be
`0` and allow no step at all; for arguments `≥ 2` the two classes of bounds coincide, and the only
input with argument `1` is `n = 0`, `v = 1`, where `Q` is a point. -/
theorem lemma_6 :
    ∀ e : ℕ, ∃ (c : ℕ) (OM : OracleMachine),
      ∀ (n v : ℕ) (V : Set (Fin n → ℚ)), V.Finite → V.Nonempty →
      (∀ x ∈ Set.extremePoints ℝ (convexHull ℝ (qCast '' V)),
        ∃ q : Fin n → ℚ, qCast q = x ∧ (encVec q).length ≤ v) →
      ∀ O : List Bool → List Bool,
        (∀ u : Fin n → ℚ, IsOptAnswer (convexHull ℝ (qCast '' V)) u (O (encVec u)) ∧
          (O (encVec u)).length ≤ (n + v + (encVec u).length + 1) ^ e) →
        ∀ y : Fin n → ℚ, ∃ w : List Bool,
          ORunsWithin OM O (encodeNat n ++ encodeNat v ++ encVec y) w
            ((n + v + (encVec y).length + 1) ^ c) ((n + v + (encVec y).length + 1) ^ c) ∧
          IsSepAnswer (convexHull ℝ (qCast '' V)) y w ∧
          w.length ≤ (n + v + (encVec y).length + 1) ^ c := by sorry

end HMBinPacking
