-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace
-- name    : LanglandsTunnell.CubicInduction.exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/1c4f1bd7-be11-5e4a-b8fb-bf60ad4b20cd
-- title:
--   Uniform rapid decay of smoothed cuspidal L² classes on GL₃
-- statement:
--   Let $\omega$ be a homomorphism from the ideles of $\mathbb{Q}$ to $\mathbb{C}^\times$ with $\|\omega(z)\|=1$ for every idele $z$, let $a,b$ be reals and let $\Phi_0$ be a subset of $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ satisfying `IsSlabDomain a b Φ₀`, that is, $0<a<b$ and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_3(\mathbb{Q})$ acting on the adelic Haar measure of $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ restricted to the determinant slab `ideleNormDetSlab a b`. Let $\varphi$ be a smoothing kernel: $\varphi(g)=\alpha(\text{archimedean entries of }g)$ times the indicator of $\{x : \text{component}_p(x)\in K'_p \text{ for all } p\}$, where $\alpha$ is smooth with compact support contained in the invertible matrices and the $K'_p$ are compact open subgroups of $\mathrm{GL}_3(\mathbb{Q}_p)$ equal to `localMaximalCompact3` for all but finitely many $p$. Let $T$ be a continuous $\mathbb{C}$-linear endomorphism of the cuspidal subspace of $L^2$ of the slab measure restricted to $\Phi_0$, i.e. of the topological closure of the span of the $L^2$ classes of the cusp functions; here a cusp function is a continuous $F : \mathrm{GL}_3(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ that is left invariant under the global points $\mathrm{GL}_3(\mathbb{Q})$, transforms by $\omega$ under the adelic centre, is square-integrable for the restricted measure, and is cuspidal along the two unipotent radicals, in the sense that for every $g$ the double integral of $F(\mathrm{radicalP21}\,[x,y]\,g)$, respectively of $F(\mathrm{radicalP12}\,[x,y]\,g)$, against the additive adelic Haar measure conditioned on the adelic box vanishes. Assume that for every cusp function $F$ the smoothed function $x\mapsto\int \varphi(g)F(xg)\,dg$ is again a cusp function and that $T$ carries the class of $F$ to the class of the smoothed function. The conclusion is that there is a single family of constants $C_N(c,C)$, indexed by $N\in\mathbb{N}$ and reals $c,C$, such that for every $u$ in the cuspidal subspace there exists a cusp function $F$ whose $L^2$ class equals $T u$ and which satisfies the following: for every $N\in\mathbb{N}$, every $c>0$, every real $C$ and all $n,t,k\in\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ such that all finite components of $n$ and of $t$ are $1$, each finite component of $k$ lies in `localMaximalCompact3` (all entries of the matrix and of its inverse of valuation at most $1$), and at every infinite place $w$ of $\mathbb{Q}$ the component of $n$ has diagonal entries $1$, vanishing entries below the diagonal and all entries of norm at most $C$, the component of $t$ is diagonal with $c\le \mathrm{archRoot}_1(w,t)$ and $c\le \mathrm{archRoot}_2(w,t)$, and the component of $k$ is orthogonal, one has, for every infinite place $w$, $$\|F(ntk)\|\le C_N(c,C)\,\bigl(\mathrm{archRoot}_1(w,t)\,\mathrm{archRoot}_2(w,t)\bigr)^{-N}\,\|u\|.$$
--
--   This is the rapid-decay statement for cusp forms on $\mathrm{GL}_3$ in the form needed here: the image under a smoothing operator of an $L^2$ cuspidal class is represented by a continuous cuspidal function whose size on the structured set $NTK$ decays faster than any power of the product of the two simple root sizes, with constants independent of the class and depending only on the decay exponent and the two parameters bounding the unipotent and torus ranges. It feeds the treatment of the smoothing and spectral operators on the cuspidal subspace in the cubic-induction chain, in particular the stability of that subspace under the operators considered there and the production of smooth cuspidal eigenfunctions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField LanglandsTunnell.CubicInduction.SlabL2

theorem
    LanglandsTunnell.CubicInduction.exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (_hφ : IsSmoothingKernel φ)
    (T : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀))
    (hT : ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀),
      ∃ hRF : smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀,
        (T ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ :
            Carrier a b Φ₀) =
          toL2 ω a b Φ₀ ⟨smoothingOperator φ F, hRF.1⟩) :
    ∃ CN : ℕ → ℝ → ℝ → ℝ, ∀ u : ↥(cuspidalSubspace ω a b Φ₀),
      ∃ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀),
        (T u : Carrier a b Φ₀) = toL2 ω a b Φ₀ ⟨F, hF.1⟩ ∧
          ∀ (N : ℕ) (c : ℝ) (_hc : 0 < c) (C : ℝ) (n t k : AdelicGL 3 (𝓞 ℚ) ℚ)
            (_hx :
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
          ∀ w : InfinitePlace ℚ,
            (∀ i j : Fin 3,
              (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
              (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
              ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
            (∀ i j : Fin 3, i ≠ j →
              (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
            (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
                (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1),
            ∀ w : InfinitePlace ℚ,
              ‖F (n * t * k)‖ ≤ CN N c C * ((archRoot₁ ℚ w t * archRoot₂ ℚ w t) ^ N)⁻¹ * ‖u‖ := by sorry
