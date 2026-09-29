-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap
-- name    : LanglandsTunnell.CubicInduction.SlabL2.le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/21a77db2-183e-5f1a-8af4-292ffee0c912
-- title:
--   Cusp-generated stable subspaces are cuspidal and spectrally invariant
-- statement:
--   Fix a character $\omega$ of the idele units of $\mathbb{Q}$ with values in $\mathbb{C}^\times$, assumed unitary ($\|\omega(z)\|=1$ for all $z$), reals $a,b$ and a set $\Phi_0\subseteq \mathrm{GL}_3$ of the adele ring of $\mathbb{Q}$ which is a slab domain, i.e. $0<a<b$ and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_3(\mathbb{Q})$ with respect to the adelic Haar measure on $\mathrm{GL}_3$ restricted to the slab where the idele norm of the determinant lies between $a$ and $b$. Let $V$ be a $\mathbb{C}$-submodule of $L^2$ of the domain measure attached to $(a,b,\Phi_0)$ subject to three hypotheses: (i) $V$ is the topological closure of the $\mathbb{C}$-span of the $L^2$-classes of those automorphic forms for $\omega$ which are cusp functions (continuous, automorphic, and cuspidal along both $P_{21}$ and $P_{12}$ for the production pins of $\mathbb{Q}$ with empty domain datum, trivial level and unit generators over the adelic box) and whose class already lies in $V$; (ii) whenever a cusp function $F$ has class in $V$ and the right translate $x\mapsto F(xg)$ is again a cusp function, that translate has class in $V$; (iii) whenever a cusp function $F$ has class in $V$, $\varphi$ is a smoothing kernel (a smooth archimedean factor times the indicator of a level subgroup which is open and compact at each finite place and equals the standard maximal compact at all but finitely many places) and $x\mapsto\int \varphi(g)F(xg)$ is again a cusp function, that convolution has class in $V$. Let $W$ be the submodule of the cuspidal subspace obtained as the preimage of $V$ under the inclusion of the cuspidal subspace, the latter being the closure of the span of the classes of all cusp members. The conclusion is threefold: $V$ is contained in the cuspidal subspace; $W$ is closed as a subset of the cuspidal subspace; and every operator $r$ in `spectralOperators3` — that is, every spectral generator and every bounded operator adjoint to a spectral generator for the $L^2$ inner product — maps $W$ into $W$.
--
--   This is the bridge between the description of an invariant subspace of the cuspidal $L^2$ space in terms of its cusp-function members, closed under right translation and under convolution with smoothing kernels, and the operator-theoretic description used in the spectral decomposition, where invariance is recorded for the generating family of operators and their adjoints. It is used in the extraction of minimal invariant subspaces and in the identification of such a subspace with the closure of the image of its cusp-function members.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SpectralOperators3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory

theorem
LanglandsTunnell.CubicInduction.SlabL2.le_cuspidalSubspace_and_isClosed_and_invariant_spectralOperators3_of_eq_comap
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (V : Submodule ℂ (Carrier a b Φ₀))
    (_hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (_htr : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
        toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V)
    (_hsm : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V)
    (W : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)) (_hW : W = V.comap (cuspidalSubspace ω a b Φ₀).subtype) :
    V ≤ cuspidalSubspace ω a b Φ₀ ∧ IsClosed (W : Set ↥(cuspidalSubspace ω a b Φ₀)) ∧
      ∀ r ∈ spectralOperators3 ω a b Φ₀, ∀ x ∈ W, r x ∈ W := by sorry
