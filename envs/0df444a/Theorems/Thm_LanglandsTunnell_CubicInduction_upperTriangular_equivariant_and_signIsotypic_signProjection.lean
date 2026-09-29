-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_upperTriangular_equivariant_and_signIsotypic_signProjection
-- name    : LanglandsTunnell.CubicInduction.upperTriangular_equivariant_and_signIsotypic_signProjection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/4271377a-5e7f-56c5-95bd-b1fe84a6d0cc
-- title:
--   Sign projection: equivariance preserved, ε-isotypic
-- statement:
--   Fix $\nu \colon \mathrm{Fin}\,3 \to \mathbb{C}$, a sign exponent $\varepsilon \colon \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$, and a complex-valued function $F$ on $\mathrm{GL}_3$ of the adele ring of $\mathbb{Q}$ (the group `AdelicGL 3 (𝓞 ℚ) ℚ`). Here, for a real $3\times 3$ array $e$, [`WhittakerBlock.archRealLift3 e`](def/LanglandsTunnell_CubicInduction_ArchSmooth3.html#L18) denotes the element of that adelic group obtained from the matrix with adelic entries given by the archimedean inclusion of the real entries of $e$, taken as a unit when it is invertible and as the identity otherwise. The hypothesis is left equivariance along real upper-triangular matrices with positive diagonal placed at the archimedean place: for every $t \colon \mathrm{Fin}\,3 \to \mathrm{Fin}\,3 \to \mathbb{R}$ with $t_{ij} = 0$ whenever $j < i$ and $t_{ii} > 0$ for all $i$, and every $g$, one has $F(\text{archRealLift3}(t)\, g) = \bigl(\prod_{a} t_{aa}^{\,\nu_a + \rho_a}\bigr) F(g)$, where $\rho = (1,0,-1)$ and the power is the complex power of the real diagonal entry. The conclusion is a conjunction about the function $$\pi_\varepsilon F(g) = \tfrac18 \sum_{\sigma \colon \mathrm{Fin}\,3 \to \mathrm{Fin}\,2} (-1)^{\sum_a \varepsilon_a \sigma_a} F\bigl(\text{archRealLift3}(\mathrm{diag}((-1)^{\sigma_a}))\, g\bigr),$$ written out in place as a lambda term: first, $\pi_\varepsilon F$ satisfies exactly the same upper-triangular equivariance with the same character $\prod_a t_{aa}^{\nu_a+\rho_a}$; second, for every $\tau \colon \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$ and every $g$, $\pi_\varepsilon F(\text{archRealLift3}(\mathrm{diag}((-1)^{\tau_a}))\, g) = (-1)^{\sum_a \varepsilon_a \tau_a}\, \pi_\varepsilon F(g)$.
--
--   This is the elementary compatibility statement for the projection onto the $\varepsilon$-isotypic component of the action of the diagonal sign group $\{\pm 1\}^3$ at the archimedean place: such a projection does not disturb equivariance under the real upper-triangular torus-with-unipotent part, since conjugating an upper-triangular matrix by a diagonal sign matrix leaves it upper triangular with the same diagonal. It is used in the passage to sign-isotypic coefficient maps in the cubic induction, being cited by [`LanglandsTunnell.CubicInduction.eq_zero_of_read_signProjection_of_separating_stable_submodule`](thm.html#LanglandsTunnell.CubicInduction.eq_zero_of_read_signProjection_of_separating_stable_submodule), [`LanglandsTunnell.CubicInduction.exists_polynomialModel_positive_actSkew_form_of_separating_stable_submodule`](thm.html#LanglandsTunnell.CubicInduction.exists_polynomialModel_positive_actSkew_form_of_separating_stable_submodule) and [`LanglandsTunnell.CubicInduction.signProjection_read_kernel_stable_of_doubleSlotCoeffMap`](thm.html#LanglandsTunnell.CubicInduction.signProjection_read_kernel_stable_of_doubleSlotCoeffMap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_upperTriangular_equivariant_and_signIsotypic_signProjection.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.upperTriangular_equivariant_and_signIsotypic_signProjection
    (ν : Fin 3 → ℂ) (ε : Fin 3 → Fin 2) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (heq : ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, F (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * F g) :
    (∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
          (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2,
        (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) *
          F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g)) (WhittakerBlock.archRealLift3 t * g) =
            (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) *
              (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2,
        (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) *
          F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g)) g) ∧
    (∀ τ : Fin 3 → Fin 2, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2,
        (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) *
          F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g)) (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * g) =
          (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) * (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2,
        (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) *
          F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g)) g) := by sorry
