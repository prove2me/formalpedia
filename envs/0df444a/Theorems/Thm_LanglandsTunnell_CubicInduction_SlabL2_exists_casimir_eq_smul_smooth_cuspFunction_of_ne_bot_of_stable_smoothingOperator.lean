-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator
-- name    : LanglandsTunnell.CubicInduction.SlabL2.exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/7b24c7d1-aab0-54f2-97a3-b32173302327
-- title:
--   A joint Casimir eigenfunction in a smoothing-stable cuspidal subspace
-- statement:
--   Let $\omega$ be a homomorphism from the ideles $(\mathbb{A}_{\mathbb{Q}})^{\times}$ to $\mathbb{C}^{\times}$ with $\|\omega(z)\|=1$ for all $z$, let $a,b\in\mathbb{R}$, and let $\Phi_0\subseteq \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ satisfy `IsSlabDomain a b Φ₀`, i.e. $0<a<b$ and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_3(\mathbb{Q})$ under `globalPointsGL` with respect to the slab measure attached to $a,b$. Let $V$ be a $\mathbb{C}$-submodule of $L^2(\mathrm{domainMeasure}\ a\ b\ \Phi_0)$ such that: $V$ is the topological closure of the span of the classes `toL2 ω a b Φ₀ f` of those $f$ in the automorphic submodule whose underlying function is a cusp function (continuous, in the automorphic submodule, and cuspidal along the two unipotent radicals recorded by `IsCuspidalAlongP21` and `IsCuspidalAlongP12` for the pin data `productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)`) and whose class already lies in $V$; $V\neq 0$; and $V$ is stable under smoothing, in the sense that for every cusp function $F$ with class in $V$ and every smoothing kernel $\varphi$ (a smooth archimedean factor in the real entries times the indicator of a product over the finite places of open compact subgroups, almost all equal to the local maximal compact) such that $\mathrm{smoothingOperator}\,\varphi\,F : x\mapsto\int \varphi(g)F(xg)\,dg$ is again a cusp function, the class of $\mathrm{smoothingOperator}\,\varphi\,F$ lies in $V$. Then there exist $c_1,c_2,c_3\in\mathbb{C}$ and a cusp function $G$ whose class lies in $V$ and is non-zero, such that $G$ is archimedean-smooth (for each $g$, $e\mapsto G(g\cdot \mathrm{archRealLift3}\,e)$ is $C^\infty$ on $\{\det e\neq 0\}$), every iterated archimedean derivative $\mathrm{archDeriv}\,i_1 j_1\cdots$ of $G$ along a finite list of index pairs is continuous, and $G$ is a joint eigenfunction of the three central operators: $\mathrm{casimir1}\,G=c_1 G$, $\mathrm{casimir2}\,G=c_2 G$, $\mathrm{casimir3}\,G=c_3 G$, where $\mathrm{casimir1}=\sum_i \partial_{ii}$, $\mathrm{casimir2}=\sum_{i,j}\partial_{ij}\partial_{ji}$ and $\mathrm{casimir3}=\sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}$ in terms of the right derivatives $\partial_{ij}=\mathrm{archDeriv}\,i\,j$ at the infinite place.
--
--   This is the existence of a smooth joint eigenfunction of the linear, quadratic and cubic central elements of $U(\mathfrak{gl}_3)$ inside a closed, cusp-generated, smoothing-stable piece of the cuspidal $L^2$-spectrum of $\mathrm{GL}_3$ over $\mathbb{Q}$; neither translation stability nor minimality of $V$ is assumed. It feeds the passage from an irreducible cuspidal constituent to its infinitesimal character, via `exists_casimir_eq_smul_of_irreducible_cuspidal`, in the construction of the cuspidal automorphic representations of $\mathrm{GL}_3$ used in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory

theorem
LanglandsTunnell.CubicInduction.SlabL2.exists_casimir_eq_smul_smooth_cuspFunction_of_ne_bot_of_stable_smoothingOperator
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ : IsSlabDomain a b Φ₀)
    (V : Submodule ℂ (Carrier a b Φ₀))
    (hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (hne : V ≠ ⊥)
    (hsm : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V) :
    ∃ (c₁ c₂ c₃ : ℂ) (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀),
      toL2 ω a b Φ₀ ⟨G, hG.1⟩ ∈ V ∧ toL2 ω a b Φ₀ ⟨G, hG.1⟩ ≠ 0 ∧
        WhittakerBlock.IsArchSmooth3 G ∧
        (∀ l : List (Fin 3 × Fin 3), Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) G)) ∧
        WhittakerBlock.casimir1 G = c₁ • G ∧ WhittakerBlock.casimir2 G = c₂ • G ∧
          WhittakerBlock.casimir3 G = c₃ • G := by sorry
