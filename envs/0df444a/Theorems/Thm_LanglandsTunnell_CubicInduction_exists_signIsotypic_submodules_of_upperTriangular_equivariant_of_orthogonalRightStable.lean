-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_signIsotypic_submodules_of_upperTriangular_equivariant_of_orthogonalRightStable
-- name    : LanglandsTunnell.CubicInduction.exists_signIsotypic_submodules_of_upperTriangular_equivariant_of_orthogonalRightStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/991ec585-b9a7-5c27-8e57-4932c201adfe
-- title:
--   Sign-isotypic splitting of a B⁺-equivariant adelic function space
-- statement:
--   Fix $\nu : \mathrm{Fin}\,3 \to \mathbb{C}$, scalars $\lambda_1,\lambda_2,\lambda_3 \in \mathbb{C}$, a $\mathbb{C}$-submodule $V$ of the space of functions $GL_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$, and an element $k_1$ of $GL_3(\mathbb{A}_{\mathbb{Q}})$ whose archimedean component `archComponent3` is $1$. Assume of every $G \in V$: $G$ is continuous; $G$ is archimedean-smooth in the sense that for each $g$ the map $e \mapsto G(g\cdot\,$`archRealLift3`$\,e)$ is $C^{\infty}$ on the real $3\times 3$ matrices of nonzero determinant, and $G$ is an eigenfunction with eigenvalues $\lambda_1,\lambda_2,\lambda_3$ of the three operators built from the archimedean right derivatives $D_{ij}$ along $1+sE_{ij}$, namely $\sum_i D_{ii}$, $\sum_{i,j} D_{ij}D_{ji}$ and $\sum_{i,j,k} D_{ij}D_{jk}D_{ki}$; $G(\,$`archRealLift3`$\,t\cdot g) = \bigl(\prod_a t_{aa}^{\nu_a + \rho_a}\bigr) G(g)$ for all real upper-triangular $t$ with positive diagonal, where $\rho = (1,0,-1)$; the right translate $g \mapsto G(gk')$ lies in $V$ whenever $k'$ has trivial component `componentAt3` at every height-one prime and archimedean component in `orth3`, i.e. satisfying $k^{\mathrm{T}}k = 1$; all such translates of $G$ lie in the span of one finite set; and for each pair $(c_0,d_0)$ there is $G' \in V$ with $s \mapsto G(g\cdot\,$`archRealLift3`$(1+sE_{c_0 d_0}))$ having derivative $G'(g)$ at $0$, for all $g$. Assume finally $F \in V$ and a real $o$ with $\sum_a o_{ai}o_{aj} = \delta_{ij}$ such that $F(\,$`archRealLift3`$\,o \cdot k_1) \neq 0$. The conclusion produces a family $V_\varepsilon$ of submodules indexed by $\varepsilon : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$, each satisfying all six properties above, each whose members satisfy in addition $G(\mathrm{diag}((-1)^{\sigma_a})_\infty \cdot g) = (-1)^{\sum_a \varepsilon_a \sigma_a} G(g)$ for all $\sigma$, and each of whose members has the form $g \mapsto \tfrac18 \sum_{\sigma} (-1)^{\sum_a \varepsilon_a \sigma_a} F'(\mathrm{diag}((-1)^{\sigma_a})_\infty \cdot g)$ for some $F' \in V$; moreover some $\varepsilon$, some $G \in V_\varepsilon$ and some real $o$ with $\sum_a o_{ai}o_{aj} = \delta_{ij}$ satisfy $G(\,$`archRealLift3`$\,o\cdot k_1) \neq 0$.
--
--   This is the decomposition of a space equivariant only under the identity component of the minimal parabolic of $GL_3(\mathbb{R})$ into isotypic pieces for the group of diagonal sign matrices, the eight projections being given by character theory of $(\mathbb{Z}/2)^3$; each piece retains the continuity, smoothness, Casimir-eigenvalue, equivariance, stability, finiteness and derivative-closure properties, and at least one piece is still nonvanishing at an orthogonal translate of $k_1$. It is used by [`LanglandsTunnell.CubicInduction.exists_transitionStable_families_ne_bot_of_inducedPicture_package_top`](thm.html#LanglandsTunnell.CubicInduction.exists_transitionStable_families_ne_bot_of_inducedPicture_package_top) to pass from a $B^{+}$-equivariant space to pieces carrying a definite character of the sign group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_signIsotypic_submodules_of_upperTriangular_equivariant_of_orthogonalRightStable.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_signIsotypic_submodules_of_upperTriangular_equivariant_of_orthogonalRightStable
    (ν : Fin 3 → ℂ) (lam₁ lam₂ lam₃ : ℂ) (V : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (hcont : (∀ G ∈ V, Continuous G))
    (hcas : (∀ G ∈ V, WhittakerBlock.IsArchSmooth3 G ∧ WhittakerBlock.casimir1 G = lam₁ • G ∧
        WhittakerBlock.casimir2 G = lam₂ • G ∧ WhittakerBlock.casimir3 G = lam₃ • G))
    (heq : (∀ G ∈ V, ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, G (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * G g))
    (hstab : (∀ G ∈ V, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) →
        archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 → (fun g => G (g * k')) ∈ V))
    (hfin : (∀ G ∈ V, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => G (g * k')) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))))
    (hflow : (∀ G ∈ V, ∀ c₀ d₀ : Fin 3, ∃ G' ∈ V, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        HasDerivAt (fun s : ℝ => G (g * WhittakerBlock.archRealLift3 fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = c₀ ∧ b = d₀ then s else 0)) (G' g) 0))
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ V)
    (hne : ∃ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ F (WhittakerBlock.archRealLift3 o * k₁) ≠ 0) :
    ∃ Vf : (Fin 3 → Fin 2) → Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ ε : Fin 3 → Fin 2,
      (∀ G ∈ Vf ε, Continuous G) ∧
      (∀ G ∈ Vf ε, WhittakerBlock.IsArchSmooth3 G ∧ WhittakerBlock.casimir1 G = lam₁ • G ∧
        WhittakerBlock.casimir2 G = lam₂ • G ∧ WhittakerBlock.casimir3 G = lam₃ • G) ∧
      (∀ G ∈ Vf ε, ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, G (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * G g) ∧
      (∀ G ∈ Vf ε, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) →
        archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 → (fun g => G (g * k')) ∈ Vf ε) ∧
      (∀ G ∈ Vf ε, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => G (g * k')) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
      (∀ G ∈ Vf ε, ∀ c₀ d₀ : Fin 3, ∃ G' ∈ Vf ε, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        HasDerivAt (fun s : ℝ => G (g * WhittakerBlock.archRealLift3 fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = c₀ ∧ b = d₀ then s else 0)) (G' g) 0) ∧
      (∀ G ∈ Vf ε, ∀ σ : Fin 3 → Fin 2, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        G (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g) =
          (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) * G g) ∧
      (∀ G ∈ Vf ε, ∃ F ∈ V, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        G g = (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) *
          F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g))) ∧
      ∃ ε : Fin 3 → Fin 2, ∃ G ∈ Vf ε, ∃ o : Fin 3 → Fin 3 → ℝ,
        (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ G (WhittakerBlock.archRealLift3 o * k₁) ≠ 0 := by sorry
