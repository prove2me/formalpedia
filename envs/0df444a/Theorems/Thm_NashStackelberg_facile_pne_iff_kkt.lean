-- Prove2me | Theorems.Thm_NashStackelberg_facile_pne_iff_kkt
-- name    : NashStackelberg.facile_pne_iff_kkt
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:46.172369+00:00
-- url     : https://prove2.me/theorems/cdea0524-5f80-492c-8e10-8e9b3e3fa9f1
-- title:
--   §3.1, p.7 — the PNEs of a facile game are exactly the joint KKT (LCP) points
-- statement:
--   Consider a **facile** simultaneous game: player $i$ minimizes
--   $$
--   f^i(x)=\tfrac12 (x^i)^\top Q^i x^i+(c^i)^\top x^i+\Big(\sum_{j\ne i}C^{ij}x^j\Big)^{\!\top}x^i
--   $$
--   over the polyhedron $\mathcal F^i=\{v: A^i v\le b^i\}$, where $Q^i$ is positive semidefinite. Then a profile $x=(x^1,\dots,x^n)$ is a pure Nash equilibrium if and only if, for every player $i$, $A^ix^i\le b^i$ and there is a multiplier vector $\lambda^i$ with
--   $$
--   \tfrac12\big(Q^i+(Q^i)^\top\big)x^i+c^i+\sum_{j\ne i}C^{ij}x^j+(A^i)^\top\lambda^i=0,
--   \qquad 0\le\lambda^i\ \perp\ b^i-A^ix^i\ge 0 .
--   $$
--
--   These conditions are the KKT conditions of all players' problems taken together. They form a mixed linear complementarity problem, which is how Step 4 of Algorithm 1 finds a pure equilibrium of the convexified game $\widetilde N$: since each player's problem is a convex quadratic program with linear constraints, its KKT conditions are necessary and sufficient for optimality.
--
--   **Formalization Note** $\tfrac12(Q^i+(Q^i)^\top)x^i$ is the gradient of $\tfrac12(x^i)^\top Q^ix^i$; $Q^i$ need not be symmetric. Player $i$'s variables are indexed by an arbitrary finite type.
--
--   Differences from the source:
--   - reading: the KKT conditions "could be reformulated as an LCP involving a matrix M and a vector q" → the explicit KKT system with complementarity 0 ≤ λⁱ ⊥ bⁱ − Aⁱxⁱ ≥ 0; reason: an existential over (M, q) would be trivially true; the KKT system is the content the page attributes to the LCP
--   - generalization: Qⁱ a positive semi-definite matrix → vᵀQⁱv ≥ 0 for all v, Qⁱ not required to be symmetric, gradient ½(Qⁱ + (Qⁱ)ᵀ)xⁱ; reason: covers every symmetric PSD matrix, for which the gradient is Qⁱxⁱ
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, §3.1, p.7, paragraph after Definition 2 (citing [22])

import Mathlib
import Definitions.Def_NashStackelberg_IsPNE

open Matrix

namespace NashStackelberg

/-- **The PNEs of a facile game are the joint KKT points** (Carvalho, Dragotto, Feijoo, Lodi &
Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, §3.1, p.7: "Whenever P is a
facile Nash game, each player's problem is convex in its variables. Therefore, the set of points
x = (x¹, …, xⁿ) concurrently satisfying the KKT conditions of every problem Pⁱ form the set of
PNEs for P", citing [22]).

A facile simultaneous game: player `i` minimizes
`fⁱ(x) = ½ (xⁱ)ᵀ Qⁱ xⁱ + (cⁱ)ᵀ xⁱ + (Σ_{j≠i} Cⁱʲ xʲ)ᵀ xⁱ` over the polyhedron
`𝓕ⁱ = {v : Aⁱ v ≤ bⁱ}`, with `Qⁱ` positive semidefinite. A profile `x` is a PNE if and only if, for
every player `i`, `xⁱ` is feasible and there is a multiplier `λⁱ ≥ 0` with
`½ (Qⁱ + (Qⁱ)ᵀ) xⁱ + cⁱ + Σ_{j≠i} Cⁱʲ xʲ + (Aⁱ)ᵀ λⁱ = 0` and `0 ≤ λⁱ ⊥ (bⁱ − Aⁱ xⁱ) ≥ 0`.

**Formalization Note.** The page continues "Equivalently, these conditions could be reformulated
as an LCP involving a matrix M and a vector q"; the KKT/complementarity system is stated explicitly
(an existential over `(M, q)` would be trivially true). `½ (Qⁱ + (Qⁱ)ᵀ) xⁱ` is the gradient of
`½ (xⁱ)ᵀ Qⁱ xⁱ`; `Qⁱ` need not be symmetric. -/
theorem facile_pne_iff_kkt {n : ℕ} {V : Fin n → Type*} [∀ i, Fintype (V i)]
    (Q : (i : Fin n) → Matrix (V i) (V i) ℝ)
    (hQ : ∀ i (v : V i → ℝ), 0 ≤ v ⬝ᵥ (Q i *ᵥ v))
    (c : (i : Fin n) → V i → ℝ) (C : (i j : Fin n) → Matrix (V i) (V j) ℝ)
    (p : Fin n → ℕ) (A : (i : Fin n) → Matrix (Fin (p i)) (V i) ℝ) (b : (i : Fin n) → Fin (p i) → ℝ)
    (x : (i : Fin n) → V i → ℝ) :
    IsPNE (fun i => {v | A i *ᵥ v ≤ b i})
        (fun i y => (1 / 2 : ℝ) * (y i ⬝ᵥ (Q i *ᵥ y i)) + c i ⬝ᵥ y i
          + (∑ j ∈ Finset.univ.erase i, C i j *ᵥ y j) ⬝ᵥ y i) x ↔
      ∀ i, A i *ᵥ x i ≤ b i ∧
        ∃ lam : Fin (p i) → ℝ, 0 ≤ lam ∧
          (1 / 2 : ℝ) • ((Q i + (Q i)ᵀ) *ᵥ x i) + c i
            + ∑ j ∈ Finset.univ.erase i, C i j *ᵥ x j + (A i)ᵀ *ᵥ lam = 0 ∧
          lam ⬝ᵥ (b i - A i *ᵥ x i) = 0 := by sorry

end NashStackelberg
