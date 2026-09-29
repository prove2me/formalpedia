-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_exists_norm_le_mul_inv_one_add_norm_sq_pow_mul_indicator_integralFiniteAdeles_of_mem_schwartzBruhat2
-- name    : NumberField.AdelicFourier.exists_norm_le_mul_inv_one_add_norm_sq_pow_mul_indicator_integralFiniteAdeles_of_mem_schwartzBruhat2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/3712aa68-cd9d-5379-894d-7feef6f4db36
-- title:
--   Standard majorant for Schwartz–Bruhat functions on A_F²
-- statement:
--   Let $F$ be a number field, and let $\Psi$ be a complex-valued function on $(\mathbb{A}_F)^2$, where $\mathbb{A}_F$ denotes the adele ring of $F$ built from $\mathcal{O}_F$ and a pair of adeles is encoded as a function on `Fin 2`. Assume $\Psi$ lies in `schwartzBruhat2 F`, that is, in the $\mathbb{C}$-linear span of the pure tensors: functions of the form $x \mapsto g\bigl(i \mapsto \iota(x_i)_\infty\bigr)\, h\bigl(i \mapsto (x_i)_f\bigr)$ with $g$ a Schwartz function on $(\text{mixed space of } F)^2$, $\iota$ the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace` identifying the infinite adeles with the mixed space $\prod_{v\ \mathrm{real}}\mathbb{R}\times\prod_{v\ \mathrm{complex}}\mathbb{C}$, and $h$ a locally constant, compactly supported function of the two finite-adelic components. Let $M$ be a natural number. Then there exist a real $C \ge 0$ and a natural number $n > 0$ such that for every $x \in (\mathbb{A}_F)^2$ one has $$\|\Psi(x)\| \le C\bigl(1 + \|(\iota((x_i)_\infty))_{i}\|^2\bigr)^{-M}\cdot \mathbf{1}\bigl[\,n\,(x_i)_f \in \widehat{\mathcal{O}}_F \text{ for } i = 0,1\,\bigr],$$ where the norm of the archimedean part is taken in $(\text{mixed space})^2$, $\widehat{\mathcal{O}}_F$ is the set `integralFiniteAdeles` of finite adeles $y$ with $y_v$ in the ring of integers of the completion at every $v$ in the height-one spectrum of $\mathcal{O}_F$, and the indicator takes the value $1$ on that set and $0$ elsewhere.
--
--   This is the standard majorant used to control Schwartz–Bruhat functions of two adelic variables: arbitrary polynomial decay at the archimedean places, times the indicator of a box $n^{-1}\widehat{\mathcal{O}}_F^2$ at the finite places. It is the integrability input for the finiteness of the weighted integral of $\Psi$ over a twisted centralizer against a power of the idele norm of the determinant, in the Godement-section construction of automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_exists_norm_le_mul_inv_one_add_norm_sq_pow_mul_indicator_integralFiniteAdeles_of_mem_schwartzBruhat2.lean

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox IsDedekindDomain
open scoped Classical

theorem NumberField.AdelicFourier.exists_norm_le_mul_inv_one_add_norm_sq_pow_mul_indicator_integralFiniteAdeles_of_mem_schwartzBruhat2
    (F : Type) [Field F] [NumberField F]
    (Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΨ : Ψ ∈ schwartzBruhat2 F) (M : ℕ) :
    ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧ 0 < n ∧ ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
      ‖Ψ x‖ ≤ C * ((1 + ‖fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1‖ ^ 2) ^ M)⁻¹ *
        Set.indicator {x : Fin 2 → AdeleRing (𝓞 F) F |
            ∀ i, ((n : ℕ) : FiniteAdeleRing (𝓞 F) F) * (x i).2 ∈ integralFiniteAdeles (𝓞 F) F}
          (fun _ => (1 : ℝ)) x := by sorry
