-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3
-- name    : LanglandsTunnell.CubicInduction.SlabL2.eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/cf688a11-e483-51da-8c49-98c2ec0f8b82
-- title:
--   Spectrally invariant closed subspaces: cusp generation and translation stability
-- statement:
--   Fix a homomorphism $\omega$ from the ideles $(\mathbb{A}_{\mathbb{Q}})^{\times}$ to $\mathbb{C}^{\times}$, all of whose values have absolute value $1$, real numbers $a,b$, and a subset $\Phi_0$ of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ which is a slab domain, i.e. $0<a<b$ and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_3(\mathbb{Q})$ acting on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ with respect to the adelic Haar measure restricted to the slab cut out by the idele norm of the determinant between $a$ and $b$. Let $W$ be a $\mathbb{C}$-submodule of the cuspidal subspace `cuspidalSubspace` $\omega\,a\,b\,\Phi_0$ — the closure of the span, inside the carrier $L^2(\mathbb{C},2,\text{domainMeasure})$, of the classes `toL2` of those automorphic members whose underlying function is continuous, lies in the automorphic submodule and is cuspidal along both `IsCuspidalAlongP21` and `IsCuspidalAlongP12` for the standard production pins — and assume $W$ is closed as a subset and stable under every operator in `spectralOperators3` $\omega\,a\,b\,\Phi_0$, that is, under the spectral generators together with all continuous endomorphisms $T$ satisfying $\langle Tx,y\rangle=\langle x,Sy\rangle$ for some spectral generator $S$. Let $V$ be a $\mathbb{C}$-submodule of the carrier equal to the image of $W$ under the inclusion of the cuspidal subspace. Then three statements hold simultaneously: first, $V$ is the topological closure of the $\mathbb{C}$-span of the `toL2` classes of those cusp members $f$ with $\mathrm{toL2}(f)\in V$; second, for every cusp function $F$ with class in $V$ and every $g\in\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ such that the right translate $x\mapsto F(xg)$ is again a cusp function, that translate has class in $V$; third, for every cusp function $F$ with class in $V$ and every smoothing kernel $\varphi$ (a smooth archimedean factor times the indicator of a level subgroup which is open and compact at each finite place and equals `localMaximalCompact3` at all but finitely many), if $x\mapsto\int\varphi(g)F(xg)\,dg$ is again a cusp function then its class lies in $V$.
--
--   This is the passage from the operator-theoretic description of an invariant subspace of the cuspidal $L^2$-space of $\mathrm{GL}_3$ over $\mathbb{Q}$ back to the description by cusp functions: the three conclusions are exactly the hypotheses in which such a subspace is later handled. It is used in the construction of minimal invariant subspaces stable under right translation and under smoothing operators, on the way to the spectral decomposition employed in the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SpectralOperators3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory

theorem
LanglandsTunnell.CubicInduction.SlabL2.eq_topologicalClosure_and_stable_of_eq_map_of_invariant_spectralOperators3
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (W : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)) (_hWc : IsClosed (W : Set ↥(cuspidalSubspace ω a b Φ₀)))
    (_hWi : ∀ r ∈ spectralOperators3 ω a b Φ₀, ∀ x ∈ W, r x ∈ W)
    (V : Submodule ℂ (Carrier a b Φ₀)) (_hV : V = W.map (cuspidalSubspace ω a b Φ₀).subtype) :
      V = (Submodule.span ℂ
        (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure ∧
      (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
        ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
          toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V) ∧
      (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
        ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
          toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V) := by sorry
