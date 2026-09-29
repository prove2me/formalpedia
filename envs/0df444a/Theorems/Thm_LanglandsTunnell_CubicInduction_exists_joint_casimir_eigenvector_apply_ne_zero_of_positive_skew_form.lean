-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_joint_casimir_eigenvector_apply_ne_zero_of_positive_skew_form
-- name    : LanglandsTunnell.CubicInduction.exists_joint_casimir_eigenvector_apply_ne_zero_of_positive_skew_form
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/3fb7c501-bf72-5c90-82e3-5f56cd5b0e2f
-- title:
--   Joint Casimir eigenvector with non-vanishing coefficient functional
-- statement:
--   Let $M$ be a complex subspace of the space of functions $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ (the group being `AdelicGL 3 (𝓞 ℚ) ℚ`), assume every $w \in M$ satisfies [`WhittakerBlock.IsArchSmooth3`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L21), i.e. for each $g$ the function $e \mapsto w(g \cdot \mathrm{archRealLift3}\,e)$ is $C^\infty$ on the set of real $3\times 3$ arrays of non-zero determinant, and assume $M$ is stable under the nine operators $\partial_{ij} =$ `WhittakerBlock.archDeriv i j`, where $(\partial_{ij}w)(g)$ is the derivative at $s=0$ of $s \mapsto w(g\cdot \mathrm{archRealLift3}(\mathrm{id} + s e_{ij}))$. Assume further (h10) that there is a form $B$ on functions which on $M$ satisfies $B(w',w) = \overline{B(w,w')}$, is additive and $\mathbb{C}$-linear in its first argument, has $\operatorname{Re} B(w,w) > 0$ for $0 \neq w \in M$, makes each $\partial_{ij}$ skew, $B(\partial_{ij}w,w') = -B(w,\partial_{ij}w')$, and is invariant under right translation by any $k \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ whose component at every height-one prime of $\mathcal{O}_{\mathbb{Q}}$ is $1$ and whose archimedean component lies in `orth3`, i.e. satisfies $k^{\mathsf T}k = 1$; and (h11) that there are monic polynomials, given by coefficients $a_1 : \mathrm{Fin}(N_1+1) \to \mathbb{C}$, $a_2$, $a_3$ with top coefficients $1$, such that for every $w \in M$ one has $\sum_l a_i(l)\,\mathrm{casimir}_i^{[l]}(w) = 0$ for $i=1,2,3$, where $\mathrm{casimir}_1 = \sum_i \partial_{ii}$, $\mathrm{casimir}_2 = \sum_{i,j}\partial_{ij}\partial_{ji}$ and $\mathrm{casimir}_3 = \sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}$. Let $A$ assign to a function $w$, a real number $y_2$ and a group element $k$ a complex number $A\,w\,y_2\,k$, and assume $A$ is $\mathbb{C}$-linear in its first argument on $M$ for all $y_2$, $k$. Then for any $w_0 \in M$, $y_2 \in \mathbb{R}$ and $k$ with $A\,w_0\,y_2\,k \neq 0$ there exist $w \in M$ and $\lambda_1,\lambda_2,\lambda_3 \in \mathbb{C}$ with $\mathrm{casimir}_i(w) = \lambda_i w$ for $i = 1,2,3$ and $A\,w\,y_2\,k \neq 0$.
--
--   This is the standard simultaneous-diagonalisation step for a unitarisable module that is finite under the centre of the universal enveloping algebra of $\mathfrak{gl}_3$ acting by right derivatives at the archimedean place: a non-zero value of a linear functional can be moved onto a joint eigenvector of the three Casimir operators. It is used in the cubic induction, via `leadingCoeff_eq_zero_or_exists_transitionStable_family_ne_bot_of_smoothingSubmodule_re`, and relies on the commutation relations of the $\partial_{ij}$, the commutativity of the three Casimirs, and the identification of the reversed cubic word as $\mathrm{casimir}_3 + \mathrm{casimir}_1^2 - 3\,\mathrm{casimir}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_joint_casimir_eigenvector_apply_ne_zero_of_positive_skew_form.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem
LanglandsTunnell.CubicInduction.exists_joint_casimir_eigenvector_apply_ne_zero_of_positive_skew_form
    (M : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (h1 : ∀ w ∈ M, WhittakerBlock.IsArchSmooth3 w)
    (h5 : ∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M)
    (h10 :
      (∃ B : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℂ,
        (∀ w ∈ M, ∀ w' ∈ M, B w' w = (starRingEnd ℂ) (B w w')) ∧
        (∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ w' ∈ M, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') ∧
        (∀ w ∈ M, w ≠ 0 → 0 < (B w w).re) ∧
        (∀ w ∈ M, ∀ w' ∈ M, ∀ i j : Fin 3,
          B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w')) ∧
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            ∀ w ∈ M, ∀ w' ∈ M, B (fun g => w (g * k)) (fun g => w' (g * k)) = B w w'))
    (h11 :
      (∃ (N₁ N₂ N₃ : ℕ) (a₁ : Fin (N₁ + 1) → ℂ) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ),
        a₁ (Fin.last N₁) = 1 ∧ a₂ (Fin.last N₂) = 1 ∧ a₃ (Fin.last N₃) = 1 ∧
        ∀ w ∈ M,
          (∑ l, a₁ l • (WhittakerBlock.casimir1^[l] w)) = 0 ∧
          (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] w)) = 0 ∧
          (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] w)) = 0))
    (A : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (h6 : ∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
      A (z • w₁ + w₂) y₂ k = z * A w₁ y₂ k + A w₂ y₂ k)
    (w₀ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hw₀ : w₀ ∈ M) (y₂ : ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ) (hne : A w₀ y₂ k ≠ 0) :
    ∃ w ∈ M, ∃ lam₁ lam₂ lam₃ : ℂ,
      WhittakerBlock.casimir1 w = lam₁ • w ∧ WhittakerBlock.casimir2 w = lam₂ • w ∧
      WhittakerBlock.casimir3 w = lam₃ • w ∧ A w y₂ k ≠ 0 := by sorry
