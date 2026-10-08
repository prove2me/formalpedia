-- Prove2me | Theorems.Thm_FuzzyGames_Values_diag_linear_continuous
-- name    : FuzzyGames.Values.diag_linear_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:45.921185+00:00
-- url     : https://prove2.me/theorems/cf7c0176-bc7e-418b-a5b5-5fc011f770e5
-- title:
--   Theorem 8.1, proof — the diagonal maps (4) are linear, C¹-continuous and satisfy (5)
-- statement:
--   For $v\in V^n$ (a $C^1$ coalitional worth function vanishing at $0$) let
--   $$(\psi_n v)_i=\int_0^1\frac{\partial v}{\partial\tau_i}(t\tau^N)\,dt .$$
--   Then:
--
--   1. each $\psi_n:V^n\to\mathbb R^n$ is linear;
--   2. each $\psi_n$ is continuous for the $C^1$ norm on the cube: $\|\psi_n v\|\le C\|v\|_{C^1}$ for some constant $C$;
--   3. property (5) holds: for every linear operator $A:\mathbb R^m\to\mathbb R^n$ with $A\tau^M=\tau^N$ (where $\tau^M=(1,\dots,1)\in\mathbb R^m$) and every $v\in V^n$,
--   $$\psi_m(v\circ A)=A^*\,\psi_n v,\qquad (A^*c)_j=\sum_{i=1}^n (Ae_j)_i\,c_i ,$$
--   $A^*$ being the transpose of $A$.
--
--   This is the first sentence of the proof of Theorem 8.1; property (5) is the source of the symmetry and atomicity axioms.
--
--   **Formalization Note** Linearity is expressed by the existence of a family of linear maps agreeing with the formula on every $V^n$. The game $v\circ A$ is passed as an element $w\in V^m$ with $w(\sigma)=v(A\sigma)$. No restriction is placed on $A$ beyond linearity and $A\tau^M=\tau^N$; elements of $V^n$ are $C^1$ on all of $\mathbb R^n$, which makes $v\circ A$ well defined.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §8, proof of Theorem 8.1, p. 10 (first sentence), and (5)

import Mathlib
import Definitions.Def_FuzzyGames_Values_Basic

namespace FuzzyGames.Values

/-- §8, proof of Theorem 8.1 (p. 10): the maps `ψ_n` defined by (4) are linear, continuous
for the C¹ norm on the FuzzyGames.NTUCore.cube, and satisfy (5). -/
theorem diag_linear_continuous :
    ∃ ψ : (n : ℕ) → Vn n →ₗ[ℝ] (Fin n → ℝ),
      (∀ (n : ℕ) (v : Vn n), ψ n v = diagValue v.1) ∧
      (∀ n : ℕ, IsC1Continuous (ψ n)) ∧
      (∀ (n m : ℕ) (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)), A 1 = 1 →
        ∀ (v : Vn n) (w : Vn m), (∀ σ : Fin m → ℝ, w.1 σ = v.1 (A σ)) →
          ∀ j : Fin m, ψ m w j = ∑ i, A (Pi.single j 1) i * ψ n v i) := by sorry

end FuzzyGames.Values
