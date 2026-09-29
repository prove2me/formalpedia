-- Prove2me | Theorems.Thm_MvFormalGroup_End_injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card
-- name    : MvFormalGroup.End.injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/97dc2b52-7858-5d51-98c2-78ea4b3c1413
-- title:
--   Faithfulness and commutant of a formal W(κ)-action
-- statement:
--   Let $p$ be a prime, let $\kappa$ be a finite field of characteristic $p$, let $k$ be a field of characteristic $p$, and let $j\colon W(\kappa)\to k$ be a ring homomorphism from the Witt vectors of $\kappa$. Let $G$ be a one-dimensional formal group law over $k$, that is, a power series $G$ in the two variables indexed by $\mathrm{Fin}\,1\oplus\mathrm{Fin}\,1$ with vanishing constant term, with both linear coefficients equal to $1$, and satisfying the associativity identity $G(G(X,Y),Z)=G(X,G(Y,Z))$ as substitutions of multivariate power series; assume moreover `G.IsComm`, i.e. interchanging the two variables leaves $G$ unchanged. Let $\rho\colon W(\kappa)\to$ [`MvFormalGroup.End G`](def/MvFormalGroup_BasicV2.html#L242) $=$ `Hom G G` be a ring homomorphism into the endomorphism ring of $G$, such that for every $a\in W(\kappa)$ the coefficient of the single variable $X_0$ in the power series underlying $\rho(a)$ equals $j(a)$, and such that the power series underlying $\rho(p)$ is exactly $X_0^{\#\kappa}$. The conclusion is twofold: $\rho$ is injective, and every $e\in$ [`MvFormalGroup.End G`](def/MvFormalGroup_BasicV2.html#L242) with $e\cdot\rho(a)=\rho(a)\cdot e$ for all $a\in W(\kappa)$ is of the form $e=\rho(a)$ for some $a$ (uniqueness of such $a$ is not part of the conclusion, though it follows from the injectivity asserted alongside).
--
--   This is the rigidity statement of Lubin–Tate theory in its reduction-mod-$p$ form: a one-dimensional formal $W(\kappa)$-module over a field of characteristic $p$ on which the uniformiser $p$ acts by the $\#\kappa$-power map has faithful $W(\kappa)$-action, and the centraliser of $W(\kappa)$ in the endomorphism ring is $W(\kappa)$ itself. It feeds the construction of special formal $\mathcal{O}_D$-modules used in the Čerednik–Drinfeld description, via [`CerednikDrinfeld.SpecialFormalODModule.exists_ringHom_centralizer_standard_existsUnique_eq_add_mul`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_ringHom_centralizer_standard_existsUnique_eq_add_mul); the proof invokes the vanishing statement [`MvFormalGroup.coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP`](thm.html#MvFormalGroup.coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP) for homomorphisms with zero linear part in characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_End_injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem MvFormalGroup.End.injective_and_forall_exists_eq_of_forall_commute_of_toPowerSeries_eq_X_pow_card
    (p : ℕ) [Fact p.Prime] {κ : Type u} [Field κ] [Fintype κ] [CharP κ p]
    {k : Type v} [Field k] [CharP k p] (j : WittVector p κ →+* k)
    (G : MvFormalGroup 1 k) [G.IsComm] (ρ : WittVector p κ →+* MvFormalGroup.End G)
    (hρ1 : ∀ a, MvPowerSeries.coeff (Finsupp.single 0 1) ((ρ a).toPowerSeries 0) = j a)
    (hρp : (ρ (p : WittVector p κ)).toPowerSeries 0 =
      (MvPowerSeries.X 0 : MvPowerSeries (Fin 1) k) ^ Fintype.card κ) :
    Function.Injective ρ ∧
      ∀ e : MvFormalGroup.End G, (∀ a, e * ρ a = ρ a * e) → ∃ a, e = ρ a := by sorry
