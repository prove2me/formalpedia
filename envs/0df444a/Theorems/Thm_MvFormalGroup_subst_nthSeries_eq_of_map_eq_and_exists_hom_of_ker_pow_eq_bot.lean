-- Prove2me | Theorems.Thm_MvFormalGroup_subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot
-- name    : MvFormalGroup.subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/f3838b61-cb4f-53fe-ba72-394502d840f5
-- title:
--   Rigidity of formal group laws along a nilpotent thickening
-- statement:
--   Let $\pi\colon R\to S$ be a homomorphism of commutative rings in a common universe, let $\mu\in\mathbb{N}$ and assume $(\ker\pi)^{\mu+1}=\bot$, and let $p,n\in\mathbb{N}$ satisfy $(p)^n=0$ in $R$. Let $G$ be a commutative formal group law of dimension $h$ over $R$: an $h$-tuple of power series in the variables indexed by $\mathrm{Fin}\,h\oplus\mathrm{Fin}\,h$ with vanishing constant terms, linear part $X_j+Y_j$, satisfying the associativity identity, together with the symmetry instance `G.IsComm`. Write $[N]$ for `G.nthSeries N`, the $h$-tuple in $h$ variables obtained by iterating $N$ times the substitution of the previous tuple into the first group of arguments of $G$, with $N=p^{n\mu}$. The assertion is the conjunction of two statements. First, for every type $\tau$ and all families $a,b\colon\mathrm{Fin}\,h\to R[[\tau]]$ with vanishing constant terms such that $\mathrm{map}\,\pi\,(a_i)=\mathrm{map}\,\pi\,(b_i)$ for all $i$, one has $[N]_i(a)=[N]_i(b)$ for all $i$. Second, for every $g$, every formal group law $F$ of dimension $g$ over $R$, and every $\varphi\colon\mathrm{Fin}\,h\to R[[X_1,\dots,X_g]]$ with vanishing constant terms, if there is a homomorphism $f_0$ from `F.map π` to `G.map π` over $S$ whose component series are the $\mathrm{map}\,\pi\,(\varphi_i)$, then there is a homomorphism $f\colon F\to G$ over $R$ whose component series are $[N]_i(\varphi)$.
--
--   This is the rigidity lemma for formal group laws in the form used by Drinfeld and Katz: points congruent modulo a nilpotent ideal become equal after applying the multiplication-by-$p^{n\mu}$ series, and a homomorphism over $S$ whose series lift to $R$ admits, after composition with that series, a lift to a homomorphism over $R$. It is invoked in the treatment of formal modules and quasi-isogenies on the way to the Čerednik–Drinfeld uniformisation, and in the lifting statements for homomorphisms of one-dimensional formal group laws.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot
    {R S : Type u} [CommRing R] [CommRing S] (π : R →+* S) (μ : ℕ)
    (hI : RingHom.ker π ^ (μ + 1) = ⊥) (p n : ℕ) (hp : (p : R) ^ n = 0)
    {h : ℕ} (G : MvFormalGroup h R) [G.IsComm] :
    (∀ (τ : Type) (a b : Fin h → MvPowerSeries τ R),
        (∀ i, (a i).constantCoeff = 0) → (∀ i, (b i).constantCoeff = 0) →
        (∀ i, MvPowerSeries.map π (a i) = MvPowerSeries.map π (b i)) →
        ∀ i, MvPowerSeries.subst a (G.nthSeries (p ^ (n * μ)) i) =
          MvPowerSeries.subst b (G.nthSeries (p ^ (n * μ)) i)) ∧
    (∀ (g : ℕ) (F : MvFormalGroup g R) (φ : Fin h → MvPowerSeries (Fin g) R),
        (∀ i, (φ i).constantCoeff = 0) →
        (∃ f₀ : (F.map π).Hom (G.map π), ∀ i, f₀.toPowerSeries i = MvPowerSeries.map π (φ i)) →
        ∃ f : F.Hom G, ∀ i, f.toPowerSeries i = MvPowerSeries.subst φ (G.nthSeries (p ^ (n * μ)) i)) := by sorry
