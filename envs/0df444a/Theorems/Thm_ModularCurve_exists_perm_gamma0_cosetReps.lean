-- Prove2me | Theorems.Thm_ModularCurve_exists_perm_gamma0_cosetReps
-- name    : ModularCurve.exists_perm_gamma0_cosetReps
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/c0035975-cdc5-5e46-956b-99de3884fa8f
-- title:
--   Right multiplication permutes the Γ₀(ℓ) coset slots
-- statement:
--   Let $\ell$ be a prime number and let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$. Consider the family of matrices indexed by `Fin (ℓ + 1)` given by `Fin.cases`: the value at $0$ is the identity, and the value at $b+1$, for $b \in$ `Fin ℓ`, is $S\,T^{b}$, where $S$ and $T$ are the standard generators `ModularGroup.S` and `ModularGroup.T` of $\mathrm{SL}_2(\mathbb{Z})$ and $b$ is used as a natural-number exponent. Writing $r_i$ for the $i$-th member of this family, the assertion is that there exists a permutation $e$ of `Fin (ℓ + 1)` such that for every index $i$ one has $r_i\,\gamma\,r_{e(i)}^{-1} \in \Gamma_0(\ell)$, that is, the lower-left entry of this product is divisible by $\ell$ (in Mathlib's `CongruenceSubgroup.Gamma0` this is the condition that the $(1,0)$ entry reduces to $0$ in $\mathbb{Z}/\ell$). No restriction such as $\ell > 2$ is imposed.
--
--   The family $1, S T^{b}$ ($b < \ell$) is the classical complete set of representatives for the right cosets $\Gamma_0(\ell)\backslash\mathrm{SL}_2(\mathbb{Z})$, whose bottom rows realise the $\ell+1$ points of $\mathbb{P}^1(\mathbb{F}_\ell)$; the statement records that right translation by any $\gamma$ permutes these cosets. It is used in the treatment of $\Gamma_0(\ell)$-invariant $q$-expansions and of the function field of the modular curve, for instance in the integrality and Fricke-involution statements for $j(q)$, $j(q^{\ell})$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_perm_gamma0_cosetReps.lean

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_perm_gamma0_cosetReps (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : ∃ e : Equiv.Perm (Fin (ℓ + 1)), ∀ i : Fin (ℓ + 1), (Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i : Matrix.SpecialLinearGroup (Fin 2) ℤ) * γ * (Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) (e i) : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ ∈ CongruenceSubgroup.Gamma0 ℓ := by sorry
