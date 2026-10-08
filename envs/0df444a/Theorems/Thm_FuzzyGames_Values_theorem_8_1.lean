-- Prove2me | Theorems.Thm_FuzzyGames_Values_theorem_8_1
-- name    : FuzzyGames.Values.theorem_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:42.492773+00:00
-- url     : https://prove2.me/theorems/9c0e88cc-badd-4aba-bcdb-571b781c57c3
-- title:
--   Theorem 8.1 — the diagonal formula is the unique sequence of fuzzy values; it satisfies (5) and picks the core of concave homogeneous games
-- statement:
--   Let $V^n$ be the space of continuously differentiable coalitional worth functions $v$ on fuzzy coalitions $\tau\in[0,1]^n$ with $v(0)=0$, normed by the $C^1$ norm of the cube. A **sequence of fuzzy values** is a family of continuous linear maps $\psi_n:V^n\to\mathbb R^n$ satisfying Pareto optimality, symmetry and atomicity.
--
--   1. There exists a sequence of fuzzy values, given by the diagonal formula
--   $$(4)\qquad \psi_n v=\int_0^1 Dv(t\tau^N)\,dt\qquad(v\in V^n).$$
--   2. It is unique: every sequence of fuzzy values $\psi'$ satisfies $\psi'_n v=\int_0^1 Dv(t\tau^N)\,dt$ for all $n\ge1$ and $v\in V^n$.
--   3. For every linear operator $A:\mathbb R^m\to\mathbb R^n$ with $A\tau^M=\tau^N$,
--   $$(5)\qquad \psi_m(v\circ A)=A^*\,\psi_n v\qquad(v\in V^n),$$
--   where $A^*$ is the transpose of $A$.
--   4. If $v\in V^n$ is moreover concave and positively homogeneous on $\mathbb R^n_+$, then $\psi_n v$ is the unique element of the core $\{c:\sum_i c_i=v(\tau^N),\ \sum_i\tau_ic_i\ge v(\tau)\ \forall\tau\in[0,1]^n\}$.
--
--   The theorem is an axiomatic characterisation of the diagonal (Aumann–Shapley) value for smooth games with fuzzy coalitions.
--
--   **Formalization Note** The paper writes "$V^N$" in the last sentence, read as $V^n$. Elements of $V^n$ are $C^1$ on all of $\mathbb R^n$ (any $C^1$ function on the cube extends), and continuity of $\psi_n$ means $\|\psi_n v\|\le C\|v\|_{C^1}$ with the $C^1$ seminorm of the cube; without this continuity uniqueness would fail. Parts 1–2 say that the formula (4) is, up to the irrelevant $n=0$ component, the only sequence of fuzzy values. Part 3 is stated for the formula (4), which by 2 is the sequence; the game $v\circ A$ is an element $w\in V^m$ with $w(\sigma)=v(A\sigma)$ and $(A^*c)_j=\sum_i(Ae_j)_ic_i$. In part 4, concavity and positive homogeneity ($v(t\tau)=tv(\tau)$, $t>0$, $\tau\ge0$) are required on the orthant $\mathbb R^n_+$, to which §2 (2) extends $v$; the core quantifies over the cube as in §2 (4)(a).
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), Theorem 8.1, p. 10

import Mathlib
import Definitions.Def_FuzzyGames_Values_Basic

namespace FuzzyGames.Values

/-- Theorem 8.1 (Aubin 1981, §8, p. 10). (i) The diagonal formula (4),
`ψ_n v = ∫_0^1 Dv(tτ^N) dt`, defines a sequence of fuzzy values; (ii) every sequence of fuzzy
values coincides with it on `V^n` for every `n ≥ 1`; (iii) property (5): for every linear
`A : ℝ^m → ℝ^n` with `Aτ^M = τ^N`, `ψ_m(v ∘ A) = A* ψ_n v`, where
`(A* c)_j = ∑_i (A e_j)_i c_i`; (iv) if `v ∈ V^n` is concave and positively homogeneous on
`ℝ^n_+`, then `ψ_n v` is the unique element of the core of `v`. -/
theorem theorem_8_1 :
    (∃ ψ : (n : ℕ) → Vn n →ₗ[ℝ] (Fin n → ℝ), IsSequenceOfFuzzyValues ψ ∧
        ∀ n : ℕ, 0 < n → ∀ v : Vn n, ψ n v = diagValue v.1) ∧
    (∀ ψ : (n : ℕ) → Vn n →ₗ[ℝ] (Fin n → ℝ), IsSequenceOfFuzzyValues ψ →
        ∀ n : ℕ, 0 < n → ∀ v : Vn n, ψ n v = diagValue v.1) ∧
    (∀ (n m : ℕ) (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)), A 1 = 1 →
        ∀ (v : Vn n) (w : Vn m), (∀ σ : Fin m → ℝ, w.1 σ = v.1 (A σ)) →
          ∀ j : Fin m, diagValue w.1 j = ∑ i, A (Pi.single j 1) i * diagValue v.1 i) ∧
    (∀ (n : ℕ) (v : Vn n), ConcaveOn ℝ (Set.Ici 0) v.1 → IsPosHomogeneous v.1 →
        FuzzyGames.TUCore.fuzzyCore v.1 = {diagValue v.1}) := by sorry

end FuzzyGames.Values
