-- Prove2me | Theorems.Thm_ModularCurve_finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self
-- name    : ModularCurve.finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/13a067e5-3078-53dd-aa67-a99efdca0f1f
-- title:
--   Finiteness of the δ'(F^⋆)²-fixed locus on Pic⁰
-- statement:
--   Fix natural numbers $p$ and $M$ with $p$ prime and $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and divisibility hypotheses $p \mid M$, $p^2 \nmid M$ (so that $M/p$ is nonzero), and let $\kappa$ be an algebraically closed field of characteristic $p$ in which every element $a$ satisfies $a^{p^n} = a$ for some $n > 0$. Write $P = \mathrm{Pic}^0_\kappa(\bar F)$ for the group of degree-zero divisor classes (finitely supported $\mathbb{Z}$-valued functions on the places of $\bar F$ over $\kappa$ of total degree zero, modulo principal divisors) of the $q$-expansion function field $\bar F =$ `Fbar p M H hpM κ` attached to the subgroup `ΓN p M H hpM` of $SL_2(\mathbb{Z})$. Let $F, F^{-1}, F^\star : P \to P$ be additive endomorphisms such that $F$ is the Frobenius push-forward `qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p`, $F^{-1}$ is a two-sided inverse of $F$, and $F^\star z = p \cdot F^{-1} z$ for all $z$. Let $\bar p \in (\mathbb{Z}/(M/p))^\times$, and let $\delta, \delta' : P \to P$ be mutually inverse additive endomorphisms with $\delta$ given by the action on $P$ of the semilinear automorphism induced by the $\kappa$-algebra automorphism `diamondActionModL` at level $M/p$ for the image subgroup `infSubgroup p M H hpM` of $H$, evaluated at the chosen $\Gamma_0(M/p)$-lift [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $\bar p$. Then the set $\{ z \in P : \delta'(F^\star(F^\star z)) = z \}$ is finite.
--
--   This is one of Ribet's two "no-eigenvalue" finiteness statements at level $\Gamma_{H'}(M/p)$: the locus of degree-zero classes fixed by an inverse diamond operator composed with the square of the Verschiebung $F^\star = p F^{-1}$ is finite. Together with its companion for $\delta F^2$ it is used to show that the push–pull map on the fibre at $p$ has finite kernel, in the form cited by [`ModularCurve.JHNeronObjectAtP.exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero`](thm.html#ModularCurve.JHNeronObjectAtP.exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero) within the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

theorem ModularCurve.finite_setOf_diamondInv_frobeniusInvSmul_sq_eq_self
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]

    (halg : ∀ a : κ, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)

    (F Finv Fstar : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ)
    (δ δ' : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL κ (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)
    (hδδ' : δ.comp δ' = AddMonoidHom.id _ ∧ δ'.comp δ = AddMonoidHom.id _) :
    {z : Pic0 κ (Fbar p M H hpM κ) | δ' (Fstar (Fstar z)) = z}.Finite := by sorry
