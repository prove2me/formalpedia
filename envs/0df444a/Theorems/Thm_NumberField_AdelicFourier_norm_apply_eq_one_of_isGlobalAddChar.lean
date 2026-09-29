-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
-- name    : NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/365f1b6a-8ba7-5f19-9091-47179a91591b
-- title:
--   Global additive characters of A_F are unitary
-- statement:
--   Let $F$ be a number field (a field `F : Type` with the `NumberField` instance), and let $\mathbb{A}_F$ denote its adele ring `AdeleRing (𝓞 F) F`, formed from the ring of integers $\mathcal{O}_F$. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$, that is, a map of the additive group of $\mathbb{A}_F$ into the multiplicative monoid of $\mathbb{C}$ sending $0$ to $1$ and sums to products. Assume `IsGlobalAddChar F ψ`, which by definition packages three conditions: $\psi$ is principal-invariant, i.e. $\psi(\iota(\alpha)) = 1$ for every $\alpha \in F$, where $\iota$ is the structure map $F \to \mathbb{A}_F$; $\psi$ is continuous; and $\psi$ is not the trivial character. Then for every adele $x \in \mathbb{A}_F$ one has $\lVert \psi(x) \rVert = 1$. Thus $\psi$ takes values in the unit circle of $\mathbb{C}$.
--
--   This is the standard unitarity of a continuous character of $\mathbb{A}_F$ trivial on $F$, reflecting the compactness of $\mathbb{A}_F/F$; it is what allows such a $\psi$ to be regarded as a character with values in the circle group. It is used throughout the adelic Fourier-analytic part of the development, in particular in the treatment of Whittaker coefficients and Rankin–Selberg integrals of automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField AutomorphicForm

theorem NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) (x : AdeleRing (𝓞 F) F) :
    ‖ψ x‖ = 1 := by sorry
