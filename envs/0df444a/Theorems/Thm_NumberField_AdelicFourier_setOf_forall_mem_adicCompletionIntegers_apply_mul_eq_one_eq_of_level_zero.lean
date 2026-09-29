-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one_eq_of_level_zero
-- name    : NumberField.AdelicFourier.setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one_eq_of_level_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/2a0bf36c-f42b-539f-8fa4-dea24571f803
-- title:
--   Level-zero additive character: the dual of mathcal Oᵥ is mathcal Oᵥ
-- statement:
--   Let $F$ be a number field, $v$ a height-one prime of its ring of integers $\mathcal O_F$ (that is, a finite place), and write $F_v$ for the $v$-adic completion `v.adicCompletion F`, with $\mathcal O_v$ its valuation subring `v.adicCompletionIntegers F`, consisting of the elements of valuation at most $1$ for the canonical $\mathbb Z_{m0}$-valued valuation `Valued.v`. Let $\psi : F_v \to \mathbb C$ be an additive character (a monoid homomorphism from the additive group of $F_v$ to $\mathbb C$). Assume two hypotheses: $\psi$ is trivial on $\mathcal O_v$, i.e. $\psi(z) = 1$ for every $z$ with valuation at most $1$; and there exists $x \in F_v$ with $\mathrm{v}(x) \le \exp(1)$, that is of valuation at most one step above the unit ball, such that $\psi(x) \ne 1$. The conclusion is an equality of subsets of $F_v$: the set of those $y \in F_v$ with $\psi(zy) = 1$ for all $z \in \mathcal O_v$ is exactly $\mathcal O_v$. In other words, for a character of level zero the annihilator of $\mathcal O_v$ under the pairing $(z,y) \mapsto \psi(zy)$ is $\mathcal O_v$ itself.
--
--   This is the computation of the dual (annihilator) box of the local integers for an additive character of conductor exponent zero, as in the local theory underlying adelic Fourier analysis. It is used in the construction of a Schwartz–Bruhat test function on the adeles whose components are standard outside a finite set of places, where the indicator of the condition $\psi_v(\mathcal O_v y) = 1$ must be identified with the indicator of $\mathcal O_v$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one_eq_of_level_zero.lean

import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.AdelicFourier.setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one_eq_of_level_zero
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (ψ : AddChar (v.adicCompletion F) ℂ)
    (h0 : ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ z = 1)
    (h1 : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ ψ x ≠ 1) :
    {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ (z * y) = 1} =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by sorry
