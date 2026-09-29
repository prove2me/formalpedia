-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_toL2_translateRight_mem_of_mem_of_isClosed
-- name    : LanglandsTunnell.CubicInduction.toL2_translateRight_mem_of_mem_of_isClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/e798b10c-0dfa-5fd5-9809-8719cf0a9b27
-- title:
--   Closed R₀-stable subspaces absorb all right translates of cusp functions
-- statement:
--   Fix a character $\omega \colon \mathbb{A}_\mathbb{Q}^\times \to \mathbb{C}^\times$ with $\|\omega(z)\| = 1$ for all $z$, reals $a, b$, and a set $\Phi_0 \subseteq \mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ which is a slab domain, i.e. $0 < a < b$ and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_3(\mathbb{Q})$ with respect to the adelic Haar measure on $\mathrm{GL}_3$ restricted to the slab where the idele norm of the determinant lies between $a$ and $b$. Here a cusp function is a continuous element of the automorphic submodule attached to $(\omega, a, b, \Phi_0)$ which is cuspidal along $P_{21}$ and along $P_{12}$ for the production pin data over $\mathbb{Q}$, and the cuspidal subspace is the topological closure of the $\mathbb{C}$-span of the images under `toL2` of the cusp members inside $L^2$ of the domain measure; each cusp function $G$ thus has a class in the cuspidal subspace. Let $R_0$ be a set of continuous $\mathbb{C}$-linear endomorphisms of the cuspidal subspace such that: (i) for every $g$ with trivial archimedean component there is $u \in R_0$ carrying, for each cusp function $G$, the class of $G$ to the class of $x \mapsto G(xg)$, which is again a cusp function; and (ii) for every smoothing kernel $\varphi$ — a smooth archimedean factor evaluated on the archimedean entries, times the indicator of the set of $x$ whose component at each finite place $p$ lies in a compact open $K'_p$, with $K'_p$ the local maximal compact for cofinitely many $p$ — there is $r \in R_0$ carrying the class of each cusp function $G$ to the class of $x \mapsto \int \varphi(y) G(xy)\,dy$, again a cusp function. Let $W$ be a $\mathbb{C}$-submodule of the cuspidal subspace which is closed as a set and satisfies $r x \in W$ for all $r \in R_0$ and $x \in W$. Then for every cusp function $G$ whose class lies in $W$, every $g \in \mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$, and every proof that $x \mapsto G(xg)$ is again a cusp function, the class of $x \mapsto G(xg)$ lies in $W$.
--
--   This is the step, in the style of Borel–Jacquet's treatment of the cuspidal spectrum, which upgrades stability of a closed subspace under finite-adelic right translations and under convolution by smoothing kernels to stability under the full adelic group: the archimedean direction is reached through an approximate identity. It is used in the analysis of the cuspidal $L^2$ space on $\mathrm{GL}_3$ over $\mathbb{Q}$, in particular in identifying closed invariant subspaces with closures of spans and in the description of irreducible cuspidal constituents via the Casimir action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_toL2_translateRight_mem_of_mem_of_isClosed.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2
open scoped InnerProductSpace

theorem
LanglandsTunnell.CubicInduction.toL2_translateRight_mem_of_mem_of_isClosed
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (_hΦ₀ : IsSlabDomain a b Φ₀)
    (R₀ : Set (↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)))
    (_hU : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ g = 1 → ∃ u ∈ R₀,
      ∀ (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀),
        ∃ hGg : translateRight g G ∈ cuspFunctions ω a b Φ₀,
          u ⟨toL2 ω a b Φ₀ ⟨G, hG.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hG⟩ =
            ⟨toL2 ω a b Φ₀ ⟨translateRight g G, hGg.1⟩,
              toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hGg⟩)
    (_hsm : ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ → ∃ r ∈ R₀,
      ∀ (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀),
        ∃ hGφ : smoothingOperator φ G ∈ cuspFunctions ω a b Φ₀,
          r ⟨toL2 ω a b Φ₀ ⟨G, hG.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hG⟩ =
            ⟨toL2 ω a b Φ₀ ⟨smoothingOperator φ G, hGφ.1⟩,
              toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hGφ⟩)
    (W : Submodule ℂ ↥(cuspidalSubspace ω a b Φ₀)) (_hWc : IsClosed (W : Set ↥(cuspidalSubspace ω a b Φ₀)))
    (_hWs : ∀ r ∈ R₀, ∀ x ∈ W, r x ∈ W)
    (G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hG : G ∈ cuspFunctions ω a b Φ₀)
    (_hGW : (⟨toL2 ω a b Φ₀ ⟨G, hG.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hG⟩ :
      ↥(cuspidalSubspace ω a b Φ₀)) ∈ W)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hGg : translateRight g G ∈ cuspFunctions ω a b Φ₀) :
    (⟨toL2 ω a b Φ₀ ⟨translateRight g G, hGg.1⟩,
      toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hGg⟩ : ↥(cuspidalSubspace ω a b Φ₀)) ∈ W := by sorry
