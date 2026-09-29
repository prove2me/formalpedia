-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_isCompactOperator_of_ne_bot_of_invariant_spectralOperators3
-- name    : LanglandsTunnell.CubicInduction.SlabL2.exists_isCompactOperator_of_ne_bot_of_invariant_spectralOperators3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/b61c4342-2d49-5d4c-9f79-1c7d1f162f7f
-- title:
--   Compact operator non-vanishing on a closed invariant subspace
-- statement:
--   Fix a character $\omega$, i.e. a group homomorphism from the units of the adele ring of $\mathbb{Q}$ to $\mathbb{C}^{\times}$, all of whose values have absolute value $1$; real numbers $a,b$; and a subset $\Phi_0$ of the adelic group $\mathrm{GL}_3$ over $\mathbb{Q}$ which is a slab domain for $(a,b)$, meaning $0<a<b$ and $\Phi_0$ is a fundamental domain for the action of the image of $\mathrm{GL}_3(\mathbb{Q})$ under the adelic embedding with respect to the slab measure (the adelic Haar measure on $\mathrm{GL}_3$ restricted to the locus where the idelic norm of the determinant lies in the slab). Work inside the cuspidal subspace $\mathrm{cuspidalSubspace}\ \omega\ a\ b\ \Phi_0$, the topological closure of the $\mathbb{C}$-span of the image, under the map `toL2` into $L^2$ of the domain measure, of those elements of the automorphic submodule whose underlying function is cuspidal. Let $W$ be a $\mathbb{C}$-submodule of this space which is closed as a set, is carried into itself by every element of $\mathrm{spectralOperators3}\ \omega\ a\ b\ \Phi_0$ — the continuous operators that are cusp lifts either of right translation by a spectral translation element or of a smoothing operator attached to a smoothing kernel, together with the operators $T$ satisfying $\langle Tx,y\rangle=\langle x,Sy\rangle$ for some such generator $S$ — and satisfies $W\neq\bot$. Then there is a continuous $\mathbb{C}$-linear operator $A$ on the cuspidal subspace which is a compact operator, which maps every closed $\mathrm{spectralOperators3}$-invariant submodule into itself, and for which $Ax\neq 0$ for some $x\in W$.
--
--   This is the input step for producing minimal closed invariant subspaces in the cuspidal $L^2$-spectrum of $\mathrm{GL}_3$ over $\mathbb{Q}$: a non-zero closed invariant subspace is detected by a compact operator that respects the whole lattice of closed invariant subspaces, so that spectral theory for compact operators becomes applicable. It is cited by [`LanglandsTunnell.CubicInduction.SlabL2.exists_le_minimal_of_isClosed_of_invariant_spectralOperators3`](thm.html#LanglandsTunnell.CubicInduction.SlabL2.exists_le_minimal_of_isClosed_of_invariant_spectralOperators3).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_isCompactOperator_of_ne_bot_of_invariant_spectralOperators3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SpectralOperators3
import Mathlib.Analysis.Normed.Operator.Compact.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField

theorem LanglandsTunnell.CubicInduction.SlabL2.exists_isCompactOperator_of_ne_bot_of_invariant_spectralOperators3
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (W : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)) (hWc : IsClosed (W : Set ↥(cuspidalSubspace ω a b Φ₀)))
    (hWi : ∀ r ∈ spectralOperators3 ω a b Φ₀, ∀ x ∈ W, r x ∈ W) (hW : W ≠ ⊥) :
    ∃ A : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀),
      IsCompactOperator A ∧
        (∀ W' : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀), IsClosed (W' : Set ↥(cuspidalSubspace ω a b Φ₀)) →
          (∀ r ∈ spectralOperators3 ω a b Φ₀, ∀ x ∈ W', r x ∈ W') → ∀ x ∈ W', A x ∈ W') ∧
        ∃ x ∈ W, A x ≠ 0 := by sorry
