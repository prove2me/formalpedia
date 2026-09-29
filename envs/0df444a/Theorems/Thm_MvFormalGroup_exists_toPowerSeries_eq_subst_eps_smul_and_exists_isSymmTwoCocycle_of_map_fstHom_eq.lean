-- Prove2me | Theorems.Thm_MvFormalGroup_exists_toPowerSeries_eq_subst_eps_smul_and_exists_isSymmTwoCocycle_of_map_fstHom_eq
-- name    : MvFormalGroup.exists_toPowerSeries_eq_subst_eps_smul_and_exists_isSymmTwoCocycle_of_map_fstHom_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/2c5463ed-9a04-5f12-b319-678e78089014
-- title:
--   First-order deformations of a commutative formal group are ε-translates by symmetric 2-cocycles
-- statement:
--   Let $k$ be a commutative ring, $n$ a natural number, and $F_0$ an $n$-dimensional formal group law over $k$: an $n$-tuple of power series $F_0^i$ in the variables indexed by $\mathrm{Fin}\,n \oplus \mathrm{Fin}\,n$ with zero constant term, whose linear coefficients in each of the two blocks are the identity matrix, satisfying associativity, and assumed commutative, i.e. $F_0(Y,X) = F_0(X,Y)$. Write $k[\varepsilon]$ for the dual numbers over $k$, $\iota : k \to k[\varepsilon]$ for the inclusion and $\pi : k[\varepsilon] \to k$ for the projection killing $\varepsilon$. For a tuple $\Gamma$ of power series in the same $2n$ variables, put $T_\Gamma^i := \iota(F_0^i)\bigl(\iota(F_0(X,Y)),\, \varepsilon\,\iota(\Gamma(X,Y))\bigr)$, the substitution of $\iota F_0^j$ for the first block of variables and of $\varepsilon \cdot \iota\Gamma^j$ for the second into $\iota F_0^i$. The assertion is a conjunction. First: for every tuple $\Gamma$ each of whose components is a symmetric $2$-cocycle for $F_0$ (zero constant term, $\Gamma(Y,X) = \Gamma(X,Y)$, and $\Gamma(F_0(X,Y),Z) + \Gamma(X,Y) = \Gamma(X,F_0(Y,Z)) + \Gamma(Y,Z)$), there exists a commutative $n$-dimensional formal group law $D$ over $k[\varepsilon]$ with $\pi_*D = F_0$ and $D^i = T_\Gamma^i$ for all $i$. Second: every commutative $n$-dimensional formal group law $F$ over $k[\varepsilon]$ with $\pi_*F = F_0$ is of the form $F^i = T_\Gamma^i$ for some tuple $\Gamma$ of symmetric $2$-cocycles for $F_0$. No uniqueness of $\Gamma$ is asserted.
--
--   This is the classical dictionary between first-order deformations of a commutative formal group law and symmetric normalised $2$-cocycles with additive values, stated in translation form so that no invariant differentials or derivatives occur. It is used in the study of deformations of special formal $\mathcal{O}_D$-modules in the Čerednik–Drinfeld setting, where tangent spaces to deformation functors over the dual numbers are computed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_exists_toPowerSeries_eq_subst_eps_smul_and_exists_isSymmTwoCocycle_of_map_fstHom_eq.lean

import Mathlib
import Definitions.Def_MvFormalGroup_TwoCocycle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.exists_toPowerSeries_eq_subst_eps_smul_and_exists_isSymmTwoCocycle_of_map_fstHom_eq
    {k : Type u} [CommRing k] {n : ℕ} (F₀ : MvFormalGroup n k) [F₀.IsComm] :
    (∀ Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k, (∀ l, F₀.IsSymmTwoCocycle (Γ l)) →
      ∃ D : MvFormalGroup n (DualNumber k), D.IsComm ∧
        D.map (TrivSqZeroExt.fstHom k k k).toRingHom = F₀ ∧
        ∀ i, D.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i))) ∧
    ∀ (F : MvFormalGroup n (DualNumber k)) [F.IsComm],
      F.map (TrivSqZeroExt.fstHom k k k).toRingHom = F₀ →
      ∃ Γ : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k, (∀ l, F₀.IsSymmTwoCocycle (Γ l)) ∧
        ∀ i, F.toPowerSeries i =
          MvPowerSeries.subst
            (Sum.elim
              (fun j => MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries j))
              fun j => (DualNumber.eps : DualNumber k) •
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (Γ j))
            (MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i)) := by sorry
