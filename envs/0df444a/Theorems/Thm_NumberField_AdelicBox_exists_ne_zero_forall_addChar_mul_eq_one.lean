-- Prove2me | Theorems.Thm_NumberField_AdelicBox_exists_ne_zero_forall_addChar_mul_eq_one
-- name    : NumberField.AdelicBox.exists_ne_zero_forall_addChar_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/58379383-5851-5471-aff5-2f5bc39b8c26
-- title:
--   Continuous characters of the finite adeles have a conductor
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal O_F$ and finite adele ring $\mathbb A_F^{f} =$ `FiniteAdeleRing (𝓞 F) F`, the restricted product of the completions $F_v$ at the height-one primes $v$ of $\mathcal O_F$ with respect to the valuation rings $\mathcal O_v$. Let $\psi_f$ be an additive character of $\mathbb A_F^{f}$ with values in $\mathbb C$, that is, a homomorphism from the additive group of $\mathbb A_F^{f}$ to the multiplicative monoid of $\mathbb C$, and assume only that $\psi_f$ is continuous (no unitarity or nonvanishing is assumed). The assertion is that there exists $d \in \mathcal O_F$ with $d \neq 0$ such that for every finite adele $z$ lying in the set `integralFiniteAdeles (𝓞 F) F`, i.e. every $z$ whose component $z_v$ belongs to $\mathcal O_v$ for all height-one primes $v$ of $\mathcal O_F$, one has $\psi_f\bigl(\iota(d)\,z\bigr) = 1$, where $\iota$ denotes the structure map $F \to \mathbb A_F^{f}$ applied to the image of $d$ in $F$. Thus $\psi_f$ is trivial on the subgroup $d\,\widehat{\mathcal O}_F$.
--
--   This is the existence of a conductor for a continuous additive character of the finite adeles: the subgroups $d\,\widehat{\mathcal O}_F$, for $d \in \mathcal O_F$ nonzero, are compact open neighbourhoods of $0$, and $\mathbb C$ has no small subgroups. It is used in the adelic Fourier-analytic development, in particular to identify a continuous character with a twist of the standard additive character and in the construction of the analytic continuation and functional equation of global zeta integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicBox_exists_ne_zero_forall_addChar_mul_eq_one.lean

import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped nonZeroDivisors

theorem NumberField.AdelicBox.exists_ne_zero_forall_addChar_mul_eq_one
    (F : Type) [Field F] [NumberField F]
    {ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ} (hψf : Continuous ψf) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
      ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) = 1 := by sorry
