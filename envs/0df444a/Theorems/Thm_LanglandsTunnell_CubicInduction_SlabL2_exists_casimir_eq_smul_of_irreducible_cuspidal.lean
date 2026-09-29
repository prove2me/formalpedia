-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_of_irreducible_cuspidal
-- name    : LanglandsTunnell.CubicInduction.SlabL2.exists_casimir_eq_smul_of_irreducible_cuspidal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/f75889e6-0601-5705-be6a-226e98d0a66b
-- title:
--   Three Casimir scalars on an irreducible cuspidal subspace
-- statement:
--   Fix a group homomorphism $\omega$ from the ideles $(\mathbb{A}_\mathbb{Q})^\times$ to $\mathbb{C}^\times$ with $\lVert\omega(z)\rVert=1$ for all $z$, real numbers $a,b$ and a subset $\Phi_0$ of $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ such that `IsSlabDomain a b Φ₀` holds, i.e. $0<a<b$ and $\Phi_0$ is a fundamental domain for the image of the global points $\mathrm{GL}_3(\mathbb{Q})$ acting on the determinant slab cut out by $a,b$, for the slab measure. Let $V$ be a $\mathbb{C}$-submodule of $L^2$ of the slab domain measure on $\Phi_0$, and write $f\mapsto$ `toL2` for the map sending an element of the automorphic submodule attached to $\omega,a,b,\Phi_0$ to its $L^2$-class. Assume: $V$ is the topological closure of the span of the classes of those cusp functions whose class already lies in $V$, where a cusp function is a member of the automorphic submodule which is continuous and cuspidal along both $P_{21}$ and $P_{12}$ for the indicated carrier pins over $\mathbb{Q}$; $V\neq 0$; $V$ is stable under right translation, in the sense that if $F$ is a cusp function with class in $V$ and $x\mapsto F(xg)$ is again a cusp function then its class lies in $V$; $V$ is likewise stable under the smoothing operators $F\mapsto \int \varphi(g)F(\,\cdot\,g)\,dg$ for every smoothing kernel $\varphi$ (a smooth archimedean factor times the indicator of a product of compact open local subgroups agreeing cofinitely with the maximal compacts); and $V$ is minimal with these properties, i.e. any submodule $W\le V$ which is the closure of the span of the classes of its own cusp functions and is stable under right translation and under smoothing operators in the same sense equals $0$ or $V$. Then there are complex numbers $c_1,c_2,c_3$ such that every cusp function $F$ whose class lies in $V$ and which satisfies `IsArchSmooth3` (for each $g$, the function $e\mapsto F(g\cdot \mathrm{archRealLift3}\,e)$ is $C^\infty$ on $\{\det e\neq 0\}$) satisfies, as an identity of functions, $\mathrm{casimir}_1F=c_1F$, $\mathrm{casimir}_2F=c_2F$, $\mathrm{casimir}_3F=c_3F$, where the $\mathrm{casimir}_k$ are the sums over $k$-cycles of indices of the iterated archimedean right derivatives $\mathrm{archDeriv}_{ij}$ in the directions $1+s\,e_{ij}$.
--
--   This is the statement that the linear, quadratic and cubic central elements of the enveloping algebra of $\mathfrak{gl}_3$, realised as right derivatives at the archimedean place, act by one fixed triple of scalars on the archimedean-smooth cusp functions belonging to an irreducible piece of the cuspidal $L^2$-spectrum of $\mathrm{GL}_3$ over the rational adeles. It feeds the construction of Whittaker-type matrix coefficients, being used in the proof that some right translate of a coset eigenfunction has nonzero inner product against the given vector.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_of_irreducible_cuspidal.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory

theorem
LanglandsTunnell.CubicInduction.SlabL2.exists_casimir_eq_smul_of_irreducible_cuspidal
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ : IsSlabDomain a b Φ₀)
    (V : Submodule ℂ (Carrier a b Φ₀))
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (hne : V ≠ ⊥)
    (htr : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
        toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V)
    (hsm : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V)
    (hmin : ∀ W : Submodule ℂ (Carrier a b Φ₀), W ≤ V →
      W = (Submodule.span ℂ
        (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ W})).topologicalClosure →
      (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ W →
        ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
          toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ W) →
      (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ W →
        ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
          toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ W) →
      W = ⊥ ∨ W = V) :
    ∃ c₁ c₂ c₃ : ℂ, ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀),
      toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V → WhittakerBlock.IsArchSmooth3 F →
        WhittakerBlock.casimir1 F = c₁ • F ∧ WhittakerBlock.casimir2 F = c₂ • F ∧
          WhittakerBlock.casimir3 F = c₃ • F := by sorry
