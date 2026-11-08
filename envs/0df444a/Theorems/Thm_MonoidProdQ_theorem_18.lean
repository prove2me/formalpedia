-- Prove2me | Theorems.Thm_MonoidProdQ_theorem_18
-- name    : MonoidProdQ.theorem_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:01:49.520115+00:00
-- url     : https://prove2.me/theorems/c8092e30-f607-4379-ab86-bc15e293b094
-- title:
--   Theorem 18 (Commutative product bound): $Q_{1/3}(\mathrm{Prod}_{M,G,n})=\Theta(\min\{n,\sqrt{n\beta_G(M)}\})$ when $1\in G$
-- statement:
--   For every finite commutative aperiodic monoid $M$, every alphabet $G\subseteq M$ and every $n\ge1$:
--
--   1. the adversary bound of the product map satisfies
--   $$\mathrm{ADV}^{\pm}(\mathrm{Prod}_{M,G,n})\le16\sqrt{n\min\{n,\beta_G(M)\}};\tag{14}$$
--   2. consequently, with a universal constant $C>0$ (the same for all $M$, $G$, $n$),
--   $$Q_{1/3}(\mathrm{Prod}_{M,G,n})\le C\min\{n,\sqrt{n\beta_G(M)}\};$$
--   3. if $1\in G$ the bound is tight: with a universal constant $c>0$,
--   $$Q_{1/3}(\mathrm{Prod}_{M,G,n})\ge c\min\{n,\sqrt{n\beta_G(M)}\},$$
--   so that $Q_{1/3}(\mathrm{Prod}_{M,G,n})=\Theta(\min\{n,\sqrt{n\beta_G(M)}\})$.
--
--   Here $\beta_G(M)$ is the product breadth (the worst-case length of a shortest product-preserving subsequence of a word over $G$, possibly infinite), $\mathrm{ADV}^{\pm}$ the negative-weight general adversary bound and $Q_{1/3}$ the bounded-error quantum query complexity with queries returning whole letters. The theorem characterizes the quantum query complexity of iterated multiplication in every finite commutative aperiodic monoid by a classical invariant, the Davenport-type constant $\beta_G(M)$.
--
--   Differences from the source:
--   - encoding: $\min\{n,\sqrt{n\beta_G(M)}\}$ and $\sqrt{n\min\{n,\beta_G(M)\}}$ → `Real.sqrt (n * (min (n : ℕ∞) (productBreadth G)).toNat)` in all three clauses; reason: $\sqrt{n\min\{n,\beta\}}=\min\{n,\sqrt{n\beta}\}$, also for $\beta=\infty$; the minimum is taken in `ℕ∞` first
--   - reading: with a universal implicit constant; $\Theta(\cdot)$ → one $C>0$ and one $c>0$, each chosen before $M$, $G$, $n$; reason: the literal meaning of universal constants
--   - encoding: $\mathrm{ADV}^{\pm}$ and $Q_{1/3}$ as numbers → `ADV±` in `ℝ≥0∞`, $Q_{1/3}$ in `ℕ∞` (cast to `ℝ≥0∞`); reason: Lean convention; suprema and infima are never junk values, and both are finite in every instance
--   - encoding: a query to index $i$ returns the entire letter $x_i$ → the platform's standard oracle $|i,y\rangle\mapsto|i,y+e_{x_i}\rangle$ with the one-hot code $e_{x_i}\in(\mathbb Z/2)^\Sigma$; reason: the paper fixes no encoding; injective encodings change query counts by at most a factor two, absorbed by the universal constants
--   - encoding: $G\subseteq M$, inputs in $G^n$ → `G : Finset M`, inputs `Fin n → ↥G`, promise domain `Finset.univ`; reason: Lean convention; $M$ is finite, so every subset is a finite set
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 18 (Commutative product bound), p.33

import Definitions.Def_MonoidProdQ_IsAperiodic
import Definitions.Def_MonoidProdQ_productBreadth
import Definitions.Def_MonoidProdQ_prodMap
import Definitions.Def_MonoidProdQ_advPm
import Definitions.Def_MonoidProdQ_Q13

open scoped ENNReal

universe u

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 18 (Commutative product bound), p.33: "For every finite commutative aperiodic
monoid M, alphabet G ⊆ M, and n ≥ 1, ADV±(Prod_{M,G,n}) ≤ 16√(n min{n, β_G(M)}). (14)
Consequently, Q_{1/3}(Prod_{M,G,n}) = O(min{n, √(nβ_G(M))}), with a universal implicit
constant. If 1 ∈ G, this bound is tight: Q_{1/3}(Prod_{M,G,n}) = Θ(min{n, √(nβ_G(M))})."
All three clauses: (a) Eq. (14); (b) the upper bound with one universal `C > 0`; (c) when
`1 ∈ G`, the matching lower bound with one universal `c > 0` (together with (b), the `Θ`).

**Formalization Note.** `min{n, β_G(M)}` is computed in `ℕ∞` (where `β_G(M)` lives) and then
converted to `ℕ` (it is finite). The bound is written `√(n · min{n, β_G(M)})`, which equals
`min{n, √(nβ_G(M))}` (also when `β_G(M) = ∞`). `Prod_{M,G,n}` is `prodMap G n` on the promise
domain `Gⁿ = Finset.univ`, the input alphabet is the subtype `↥G` and the output alphabet `M`.
`ADV±` is in `ℝ≥0∞` and `Q_{1/3}` in `ℕ∞` (cast to `ℝ≥0∞`). The constants `C`, `c` are chosen
before `M`, `G` and `n`. -/
theorem theorem_18 :
    (∀ (M : Type u) [CommMonoid M] [Fintype M] [DecidableEq M], IsAperiodic M →
      ∀ (G : Finset M) (n : ℕ), 1 ≤ n →
        advPm (prodMap G n) Finset.univ ≤
          ENNReal.ofReal (16 * Real.sqrt (n * ((min (n : ℕ∞) (productBreadth G)).toNat : ℝ)))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [CommMonoid M] [Fintype M] [DecidableEq M], IsAperiodic M →
        ∀ (G : Finset M) (n : ℕ), 1 ≤ n →
          (Q13 (prodMap G n) Finset.univ : ℝ≥0∞) ≤
            ENNReal.ofReal (C * Real.sqrt (n * ((min (n : ℕ∞) (productBreadth G)).toNat : ℝ)))) ∧
    (∃ c : ℝ, 0 < c ∧
      ∀ (M : Type u) [CommMonoid M] [Fintype M] [DecidableEq M], IsAperiodic M →
        ∀ (G : Finset M) (n : ℕ), 1 ≤ n → (1 : M) ∈ G →
          ENNReal.ofReal (c * Real.sqrt (n * ((min (n : ℕ∞) (productBreadth G)).toNat : ℝ))) ≤
            (Q13 (prodMap G n) Finset.univ : ℝ≥0∞)) := by sorry

end MonoidProdQ
