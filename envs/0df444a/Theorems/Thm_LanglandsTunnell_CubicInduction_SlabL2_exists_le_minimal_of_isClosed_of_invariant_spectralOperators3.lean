-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3
-- name    : LanglandsTunnell.CubicInduction.SlabL2.exists_le_minimal_of_isClosed_of_invariant_spectralOperators3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/20335978-65e1-5258-b8c6-bbc8c680bf5a
-- title:
--   Existence of a minimal closed invariant subspace in the cuspidal L²
-- statement:
--   Fix a homomorphism $\omega$ from the unit group of the adele ring of $\mathbb{Q}$ to $\mathbb{C}^\times$ which is unitary, i.e. $\|\omega(z)\| = 1$ for every idele $z$; real numbers $a, b$; and a subset $\Phi_0$ of $\mathrm{GL}_3$ of the adele ring of $\mathbb{Q}$ which is a slab domain for $a,b$, meaning $0 < a < b$ and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_3(\mathbb{Q})$ under the entrywise map `globalPointsGL` acting on the adelic Haar measure restricted to the determinant-norm slab `ideleNormDetSlab a b`. Let $W$ be a $\mathbb{C}$-submodule of the cuspidal subspace attached to $(\omega, a, b, \Phi_0)$ — the topological closure of the span of the images under `toL2` of the cusp members of the automorphic submodule inside $L^2$ of the domain measure — such that $W$ is closed as a set, $W \neq \bot$, and $r\,x \in W$ for every $x \in W$ and every $r$ in `spectralOperators3`, that is, every continuous endomorphism of the cuspidal subspace which either is a cusp lift of right translation by a spectral translation $h$, or a cusp lift of a smoothing operator with smoothing kernel $\varphi$, or satisfies $\langle T x, y\rangle = \langle x, S y\rangle$ for all $x,y$ with $S$ such a generator. Then there is a submodule $W_0 \le W$ which is closed, invariant under `spectralOperators3`, non-zero, and minimal among such: every submodule $W' \le W_0$ that is closed and invariant under `spectralOperators3` equals $\bot$ or $W_0$.
--
--   This is the Hilbert-space half of the decomposition of the cuspidal spectrum of $\mathrm{GL}_3$ into irreducible constituents: inside any non-zero closed subspace invariant under the spectral operator family (right translations, smoothing operators and their adjoints) one finds a minimal such subspace. It rests on the existence of a non-zero compact operator preserving all closed invariant subspaces, and is used by [`LanglandsTunnell.CubicInduction.SlabL2.exists_le_minimal_of_stable_translateRight_smoothingOperator`](thm.html#LanglandsTunnell.CubicInduction.SlabL2.exists_le_minimal_of_stable_translateRight_smoothingOperator).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_isClosed_of_invariant_spectralOperators3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SpectralOperators3
import Mathlib.Analysis.Normed.Operator.Compact.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem LanglandsTunnell.CubicInduction.SlabL2.exists_le_minimal_of_isClosed_of_invariant_spectralOperators3
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (W : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)) (_hWc : IsClosed (W : Set ↥(cuspidalSubspace ω a b Φ₀)))
    (_hWi : ∀ r ∈ spectralOperators3 ω a b Φ₀, ∀ x ∈ W, r x ∈ W) (_hW : W ≠ ⊥) :
    ∃ W₀ : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀), W₀ ≤ W ∧
      IsClosed (W₀ : Set ↥(cuspidalSubspace ω a b Φ₀)) ∧
      (∀ r ∈ spectralOperators3 ω a b Φ₀, ∀ x ∈ W₀, r x ∈ W₀) ∧ W₀ ≠ ⊥ ∧
      ∀ W' : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀), W' ≤ W₀ →
        IsClosed (W' : Set ↥(cuspidalSubspace ω a b Φ₀)) →
        (∀ r ∈ spectralOperators3 ω a b Φ₀, ∀ x ∈ W', r x ∈ W') → W' = ⊥ ∨ W' = W₀ := by sorry
