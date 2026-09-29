-- Prove2me | Theorems.Thm_MvFormalGroup_WittLaw_subst_addFam_eq_add_of_coeff_eq_ghost
-- name    : MvFormalGroup.WittLaw.subst_addFam_eq_add_of_coeff_eq_ghost
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/bb8ce8f7-b565-5449-8ddc-68bfdac61dcd
-- title:
--   Ghost series are additive for the Witt addition law
-- statement:
--   Let $p$ be a prime, $R$ a commutative ring, $c : \mathbb{N} \to R$ a sequence of coefficients and $G \in R[[X_0, X_1, \dots]]$ a power series in the variables indexed by $\mathbb{N}$. Assume that the coefficients of $G$ are those of the ghost series attached to $c$, in the precise sense that (i) for all $k, n \in \mathbb{N}$ the coefficient of $G$ at the exponent vector $\mathrm{single}\,k\,(p^{n})$, i.e. at the monomial $X_k^{p^{n}}$, equals $p^{k}\,c_{k+n}$, and (ii) the coefficient of $G$ at any exponent vector $e : \mathbb{N} \to_{f} \mathbb{N}$ which is not of the form $\mathrm{single}\,k\,(p^{n})$ vanishes; since $\mathrm{single}\,k\,(p^{n}) \ne 0$, condition (ii) in particular forces the constant coefficient of $G$ to be $0$. Thus $G = \sum_{N} c_N w_N$ with $w_N = \sum_{k \le N} p^{k} X_k^{p^{N-k}}$. The conclusion is an identity in $R[[X_{(i,m)} : i \in \mathrm{Fin}\,2,\ m \in \mathbb{N}]]$: substituting for the $n$-th variable the $n$-th Witt addition polynomial [`MvFormalGroup.WittLaw.addFam p R n`](def/MvFormalGroup_CartierModule.html#L107), namely the image under $\mathbb{Z} \to R$ of `WittVector.wittAdd p n` viewed as a power series in the variables $X_{(i,m)}$, yields the same series as the sum of the two substitutions $X_m \mapsto X_{(0,m)}$ and $X_m \mapsto X_{(1,m)}$ applied to $G$.
--
--   This says that a ghost series with coefficient sequence $c$ is a homomorphism from the Witt formal group to the additive formal group, the substitution identity $G(S(X;Y)) = G(X) + G(Y)$ for the Witt addition law $S$. It is used in the construction of logarithms and tangent data for Cartier modules, by [`MvFormalGroup.CartierModule.exists_tangent_eq_and_coeff_subst_eq_ghost_of_log`](thm.html#MvFormalGroup.CartierModule.exists_tangent_eq_and_coeff_subst_eq_ghost_of_log).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_WittLaw_subst_addFam_eq_add_of_coeff_eq_ghost.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.WittLaw.subst_addFam_eq_add_of_coeff_eq_ghost
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] (c : ℕ → R) (G : MvPowerSeries ℕ R)
    (hG : ∀ k n : ℕ, (MvPowerSeries.coeff (Finsupp.single k (p ^ n)) G : R) = (p : R) ^ k * c (k + n))
    (hG' : ∀ e : ℕ →₀ ℕ, (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) → (MvPowerSeries.coeff e G : R) = 0) :
    MvPowerSeries.subst (MvFormalGroup.WittLaw.addFam p R) G =
      MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) G +
        MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) G := by sorry
