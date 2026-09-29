-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_stable_translateRight_smoothingOperator
-- name    : LanglandsTunnell.CubicInduction.SlabL2.exists_le_minimal_of_stable_translateRight_smoothingOperator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/fb2502d7-441b-5c5a-b501-85cc6495e070
-- title:
--   Existence of a minimal cusp-generated stable subspace for GL₃
-- statement:
--   Let $\omega$ be a homomorphism from the ideles $(\mathbb{A}_{\mathbb{Q}})^{\times}$ to $\mathbb{C}^{\times}$ with $\|\omega(z)\|=1$ for all $z$, let $a,b$ be real numbers and let $\Phi_0$ be a subset of $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ which is a slab domain, i.e. $0<a<b$ and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_3(\mathbb{Q})$ acting on the adelic group with respect to the adelic Haar measure restricted to the idele-norm-determinant slab determined by $a,b$. Write $\mathrm{Carrier}$ for $L^2$ of that measure further restricted to $\Phi_0$, and `toL2` for the linear map sending an automorphic function (left $\mathrm{GL}_3(\mathbb{Q})$-invariant, transforming by $\omega$ under adelic central scalars, and $L^2$ on the domain) to its class. Let $V_0$ be a $\mathbb{C}$-submodule of $\mathrm{Carrier}$ such that: $V_0$ is the topological closure of the $\mathbb{C}$-span of the classes of those automorphic members of $V_0$ whose underlying function is a cusp function (continuous, and cuspidal along the two standard parabolic directions $P_{21}$ and $P_{12}$ for the production pins of $\mathbb{Q}$); $V_0\neq 0$; and for every cusp function $F$ with class in $V_0$ and every $g$, if the right translate $x\mapsto F(xg)$ is again a cusp function then its class lies in $V_0$, and likewise for every smoothing operator $F\mapsto \int \varphi(g)F(xg)\,dg$ with $\varphi$ a smoothing kernel (a smooth archimedean factor times the indicator of a family of open compact local subgroups agreeing with the standard maximal compacts at all but finitely many primes). Then there exists a submodule $V\le V_0$ enjoying the same three properties — being the closure of the span of the classes of its cusp members, being non-zero, and being stable under right translation and under smoothing in the above sense — and minimal among them: every $W\le V$ which is the closure of the span of the classes of its cusp members and is stable under right translation and under smoothing equals $0$ or $V$.
--
--   This is the existence half of the discrete decomposition of the cuspidal spectrum: inside a non-zero closed cusp-generated translation- and smoothing-stable subspace of the $L^2$ space on a slab fundamental domain for $\mathrm{GL}_3$ over $\mathbb{Q}$ one finds an irreducible (minimal) such subspace; no uniqueness or multiplicity statement is made. It is used in the $\mathrm{GL}_3$ input to the Langlands–Tunnell step, where a minimal piece is exploited to produce a cusp function with a non-vanishing translation matrix coefficient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_le_minimal_of_stable_translateRight_smoothingOperator.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory

theorem LanglandsTunnell.CubicInduction.SlabL2.exists_le_minimal_of_stable_translateRight_smoothingOperator
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ : IsSlabDomain a b Φ₀)
    (V₀ : Submodule ℂ (Carrier a b Φ₀))
    (_hgen : V₀ = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V₀})).topologicalClosure)
    (_hne : V₀ ≠ ⊥)
    (_htr : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V₀ →
      ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
        toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V₀)
    (_hsm : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V₀ →
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V₀) :
    ∃ V : Submodule ℂ (Carrier a b Φ₀), V ≤ V₀ ∧
      V = (Submodule.span ℂ
        (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure ∧
      V ≠ ⊥ ∧
      (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
        ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
          toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V) ∧
      (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
        ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
          toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V) ∧
      (∀ W : Submodule ℂ (Carrier a b Φ₀), W ≤ V →
        W = (Submodule.span ℂ
          (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ W})).topologicalClosure →
        (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ W →
          ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
            toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ W) →
        (∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ W →
          ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ →
            ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
              toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ W) →
        W = ⊥ ∨ W = V) := by sorry
