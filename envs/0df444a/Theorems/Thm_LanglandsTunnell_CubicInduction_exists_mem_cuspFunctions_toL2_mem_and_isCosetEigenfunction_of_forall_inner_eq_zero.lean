-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero
-- name    : LanglandsTunnell.CubicInduction.exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/7d2f682d-a1cc-5765-a4de-d08573f4f818
-- title:
--   Hecke-eigen cusp function inside an invariant L² subspace
-- statement:
--   Fix a finite set $S$ of height-one primes of $\mathcal{O}_{\mathbb{Q}}$, a character $\omega$ of the idele units with values in $\mathbb{C}^\times$ all of whose values have modulus $1$, functions $\lambda_1,\lambda_2$ from primes to $\mathbb{C}$, reals $a,b$ and a set $\Phi_0 \subseteq \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ which is a slab domain, i.e. $0<a<b$ and $\Phi_0$ is a fundamental domain for the image of the global points of $\mathrm{GL}_3$ with respect to the slab measure attached to $a,b$. Let $F$ be a cusp function for $(\omega,a,b,\Phi_0)$: it is left invariant under global points, transforms by $\omega$ under central adelic scalars, lies in $L^2$ of the domain measure, is continuous, and is cuspidal along the two parabolic directions $P_{21}$, $P_{12}$ for the indicated pin data. Assume its $L^2$ class `toL2` is non-zero, and that for every prime $p \notin S$ the function $F$ is right invariant under the image in the adelic group of the local maximal compact subgroup at $p$ and is a coset eigenfunction, with eigenvalues $\lambda_1(p)$ and $\lambda_2(p)$, for the Hecke generators $\mathrm{diag}(\varpi_p,1,1)$ and $\mathrm{diag}(\varpi_p,\varpi_p,1)$; here being a coset eigenfunction with eigenvalue $\lambda$ means that for every finite family of representatives forming a Hecke coset system for the subgroup and the generator, the corresponding coset sum equals $\lambda$ times the function. Let $V$ be a complex submodule of $L^2$ of the domain measure such that: $V$ is the topological closure of the span of the $L^2$ classes of those cusp functions whose classes already lie in $V$; $V \ne \bot$; $V$ is stable under right translation of cusp functions and under the smoothing operators attached to smoothing kernels (in both cases on cusp functions whose translate, respectively smoothed function, is again a cusp function); and orthogonality transfers, in the sense that for any cusp function $G$ with class in $V$ and any cusp function $F'$, if all right translates of the given $F$ are orthogonal to the class of $F'$, then so are all right translates of $G$. The conclusion is that there exist a finite set $S'$ of primes containing $S$ and a cusp function $F_1$ for $(\omega,a,b,\Phi_0)$ whose $L^2$ class lies in $V$ and is non-zero, and which for every $p \notin S'$ is right invariant under the image of the local maximal compact subgroup at $p$ and a coset eigenfunction for the same two Hecke generators with the same eigenvalues $\lambda_1(p)$, $\lambda_2(p)$.
--
--   This is the step that replaces a Hecke eigen cusp form by a non-zero Hecke eigen representative, with unchanged eigenvalues away from an enlarged finite set of primes, inside a prescribed closed invariant subspace of the cuspidal $L^2$ space for $\mathrm{GL}_3$ over $\mathbb{Q}$. It is used in the proof that some right translate of such a form has non-zero inner product against the subspace, in the analytic input to the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2
open scoped InnerProductSpace

theorem
LanglandsTunnell.CubicInduction.exists_mem_cuspFunctions_toL2_mem_and_isCosetEigenfunction_of_forall_inner_eq_zero
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀) (_hF0 : toL2 ω a b Φ₀ ⟨F, hF.1⟩ ≠ 0)
    (_hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F)
    (_hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) F (lam1 p))
    (_hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) F (lam2 p))
    (V : Submodule ℂ (Carrier a b Φ₀))
    (_hgen : V = (Submodule.span ℂ
      (toL2 ω a b Φ₀ '' {f | f ∈ cuspMembers ω a b Φ₀ ∧ toL2 ω a b Φ₀ f ∈ V})).topologicalClosure)
    (_hne : V ≠ ⊥)
    (_htr : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ cuspFunctions ω a b Φ₀),
        toL2 ω a b Φ₀ ⟨translateRight g F, hg.1⟩ ∈ V)
    (_hsm : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∈ V →
      ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∀ hφ : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hφ.1⟩ ∈ V)
    (_hVF : ∀ (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀), toL2 ω a b Φ₀ ⟨G, hG.1⟩ ∈ V →
      ∀ (F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF' : F' ∈ cuspFunctions ω a b Φ₀),
        (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ automorphicSubmodule ω a b Φ₀),
          ⟪toL2 ω a b Φ₀ ⟨translateRight g F, hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0) →
        ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g G ∈ automorphicSubmodule ω a b Φ₀),
          ⟪toL2 ω a b Φ₀ ⟨translateRight g G, hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 ℚ)), S ⊆ S' ∧
      ∃ (F₁ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF₁ : F₁ ∈ cuspFunctions ω a b Φ₀),
        toL2 ω a b Φ₀ ⟨F₁, hF₁.1⟩ ∈ V ∧ toL2 ω a b Φ₀ ⟨F₁, hF₁.1⟩ ≠ 0 ∧
        (∀ p, p ∉ S' → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F₁) ∧
        (∀ p, p ∉ S' → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (localToAdelic3 p (heckeGen1 p)) F₁ (lam1 p)) ∧
        (∀ p, p ∉ S' → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
          (localToAdelic3 p (heckeGen2 p)) F₁ (lam2 p)) := by sorry
