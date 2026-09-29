-- Prove2me | Theorems.Thm_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp
-- name    : ModularCurve.meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/7dd779fb-a6ef-5c32-9915-a47d3d925f0c
-- title:
--   Divisor invariance and elliptic-point divisibility for multiplicative F
-- statement:
--   Fix $N\ge 1$, a function $F:\mathfrak H\to\mathbb C$ and a weight-$2$ cusp form $k$ on $\Gamma_0(N)$. Assume first that the transported function $z\mapsto F(\mathrm{ofComplex}\,z)$ on $\mathbb C$ is meromorphic at every point $\tau\in\mathfrak H$, and second that $F$ transforms under $\Gamma_0(N)$ by the multiplier attached to the periods of $k$: for every $\gamma\in\Gamma_0(N)$ and every $\tau\in\mathfrak H$, $F(\gamma\cdot\tau)=\exp\bigl(2\pi i\,\mathrm{Re}(\,\mathrm{period}\,N\,\gamma\,k)\bigr)\,F(\tau)$, where [`ModularCurve.period N γ`](def/ModularCurve_PeriodLattice.html#L92) is the linear functional `periodAlong N I (γ • I)` on weight-$2$ cusp forms, whose value at $k$ is $\int_0^1 \mathrm{periodIntegrand}\,N\,I\,(\gamma\cdot I)\,k\,(t)\,dt$, the period of $k$ along a path from $i$ to $\gamma\cdot i$. Two conclusions follow. (1) For all $\gamma\in\Gamma_0(N)$ and $\tau\in\mathfrak H$, the meromorphic order of $z\mapsto F(\mathrm{ofComplex}\,z)$ at $\gamma\cdot\tau$ equals its order at $\tau$. (2) For every $\tau\in\mathfrak H$ and every integer $n$ such that this order at $\tau$ equals $n$ in $\mathbb Z\cup\{\infty\}$, the cardinality of the stabiliser of $\tau$ in $\Gamma_0(N)$ divides $2n$ in $\mathbb Z$.
--
--   This is the statement that a meromorphic function on $\mathfrak H$ transforming by a unitary multiplier character has a $\Gamma_0(N)$-invariant divisor, together with the local divisibility condition at elliptic points (where the stabiliser has order $2e_\tau$, so that $e_\tau$ divides the order of vanishing). It is used in the construction of an invariant untwisting of such an $F$ and in the associated statements about chains of periods and the period lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp
    {N : ℕ} [NeZero N]
    (F : ℍ → ℂ) (k : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ k).re : ℂ)) * F τ) :
    (∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) =
        meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) ∧
    (∀ (τ : ℍ) (n : ℤ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) →
        (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) : ℤ) ∣ 2 * n) := by sorry
