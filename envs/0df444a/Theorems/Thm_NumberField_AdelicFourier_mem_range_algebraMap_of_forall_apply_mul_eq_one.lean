-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_mem_range_algebraMap_of_forall_apply_mul_eq_one
-- name    : NumberField.AdelicFourier.mem_range_algebraMap_of_forall_apply_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/20073258-95df-5a73-9602-343f31ab7d07
-- title:
--   Self-annihilation of F in A_F under a global character
-- statement:
--   Let $F$ be a number field (a field of characteristic zero, finite over $\mathbb{Q}$, with ring of integers $\mathcal{O}_F$), and let $\mathbb{A}_F$ denote its adele ring, with $\iota =$ `algebraMap` the diagonal embedding $F \to \mathbb{A}_F$. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$, i.e. a monoid homomorphism from the additive group of $\mathbb{A}_F$ to the multiplicative monoid of $\mathbb{C}$, and assume `IsGlobalAddChar F ψ`, which by definition asserts three things: $\psi(\iota(\alpha)) = 1$ for every $\alpha \in F$, that $\psi$ is continuous, and that $\psi$ is not the trivial character. Let $y \in \mathbb{A}_F$ be an adele such that $\psi(y \cdot \iota(\xi)) = 1$ for every $\xi \in F$. The conclusion is that $y$ lies in the range of $\iota$, that is, $y = \iota(\xi_0)$ for some $\xi_0 \in F$. Thus, for the pairing $(x,y) \mapsto \psi(xy)$ attached to any global additive character, the annihilator of the principal adeles is exactly the principal adeles.
--
--   This is the standard self-duality statement $F^{\perp} = F$ from Tate's thesis, the inclusion $F \subseteq F^{\perp}$ being the principal-invariance of $\psi$; it is what makes the characters of $\mathbb{A}_F/\iota(F)$ be parametrised by $F$ itself. In this development it underlies the Whittaker–Fourier expansion of adelic automorphic forms, being used in [`AutomorphicForm.hasSum_whittakerCoefficient`](thm.html#AutomorphicForm.hasSum_whittakerCoefficient) and in the subsequent estimates on isotypic cuspidal windows and class sums.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_mem_range_algebraMap_of_forall_apply_mul_eq_one.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField AutomorphicForm

theorem NumberField.AdelicFourier.mem_range_algebraMap_of_forall_apply_mul_eq_one (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) (y : AdeleRing (𝓞 F) F)
    (hy : ∀ ξ : F, ψ (y * algebraMap F (AdeleRing (𝓞 F) F) ξ) = 1) :
    y ∈ Set.range (algebraMap F (AdeleRing (𝓞 F) F)) := by sorry
