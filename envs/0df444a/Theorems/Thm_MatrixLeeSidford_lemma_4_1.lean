-- Prove2me | Theorems.Thm_MatrixLeeSidford_lemma_4_1
-- name    : MatrixLeeSidford.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:34:14.658208+00:00
-- url     : https://prove2.me/theorems/1d0fd59a-2bc8-4ad5-b9be-d8226eb7e68a
-- title:
--   Lemma 4.1 — sum-of-squares bound and $E_G\subseteq K_y$
-- statement:
--   Throughout, $A_1,\dots,A_m,C$ are real symmetric $n\times n$ matrices satisfying the standing assumptions (4.3): $\Omega=\{y:S(y)\succ0\}\neq\emptyset$, the $A_i$ are linearly independent, and $\bigcap_i\ker A_i=\{0\}$.
--
--   Let $y\in\Omega$ and $G\succeq0$, let $B_i$ be the normalized constraint matrices at $y$, and set $V_a=\sum_i (G^{1/2})_{ia}B_i$ for $a=1,\dots,m$. Then
--   1. $L_y(G)=\sum_a V_a^2\succeq0$;
--   2. every $z\in\mathbb R^m$ satisfies
--   $$
--   \Big(\sum_a z_aV_a\Big)^2\preceq\|z\|_2^2\,L_y(G);
--   $$
--   3. $L_y(G)\preceq I$ implies $E_G\subseteq K_y$;
--   4. if $G\succ0$, then $L_y(G)\succ0$.
--
--   The lemma replaces the infinite family of slab constraints defining $E_G\subseteq K_y$ by the single semidefinite inequality $L_y(G)\preceq I$; this is the constraint whose trace-power penalty defines the potential.
--
--   **Formalization Note** Loewner inequalities are positive semidefiniteness of the difference; $G^{1/2}$ is the positive semidefinite square root.
--
--   Differences from the source:
--   - encoding: Aᵢ, C ∈ Sⁿ, y, h ∈ ℝᵐ → real n×n matrices with IsHermitian hypotheses; y, h ∈ EuclideanSpace ℝ (Fin m); reason: Lean representation of the same objects
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Lemma 4.1, p.33

import Mathlib
import Definitions.Def_MatrixLeeSidford_Lmap
import Definitions.Def_MatrixLeeSidford_matRpow
import Definitions.Def_MatrixLeeSidford_ellipsoid
import Definitions.Def_MatrixLeeSidford_localRegion
import Definitions.Def_MatrixLeeSidford_dualRegion

open Matrix Filter Topology
open scoped ContDiff Pointwise

namespace MatrixLeeSidford

/-- **Lemma 4.1 (Sum-of-squares bound)** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), p.33). Let `y ∈ Ω` and `G ⪰ 0`, and let
`V_a := ∑ᵢ (G^{1/2})ᵢₐ Bᵢ`. Then `L_y(G) = ∑_a V_a² ⪰ 0`, every `z ∈ ℝᵐ` satisfies
`(∑_a z_a V_a)² ⪯ ‖z‖₂² L_y(G)`, `L_y(G) ⪯ I` implies `E_G ⊆ K_y`, and `G ≻ 0` implies `L_y(G) ≻ 0`.

**Formalization Note** The standing assumptions (4.3) (p.32) are hypotheses: `Aᵢ, C` symmetric, `Ω ≠ ∅`, the `Aᵢ`
linearly independent, `⋂ᵢ ker Aᵢ = {0}`. Loewner relations are `PosSemidef` of the difference; `G^{1/2}`
is `matRpow (1/2) G`. -/
theorem lemma_4_1 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian)
    (hΩ : (dualRegion A C).Nonempty) (hlin : LinearIndependent ℝ A)
    (hker : ∀ v : Fin n → ℝ, (∀ i, A i *ᵥ v = 0) → v = 0)
    (y : EuclideanSpace ℝ (Fin m)) (hy : y ∈ dualRegion A C)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.PosSemidef) :
    let S := slack A C y
    let V : Fin m → Matrix (Fin n) (Fin n) ℝ := fun a => ∑ i, matRpow (1 / 2) G i a • normB A S i
    (Lmap A S G = ∑ a, V a ^ 2 ∧ (Lmap A S G).PosSemidef) ∧
    (∀ z : EuclideanSpace ℝ (Fin m), ((‖z‖ ^ 2) • Lmap A S G - (∑ a, z a • V a) ^ 2).PosSemidef) ∧
    ((1 - Lmap A S G).PosSemidef → ellipsoid G ⊆ localRegion A S) ∧
    (G.PosDef → (Lmap A S G).PosDef) := by sorry

end MatrixLeeSidford
