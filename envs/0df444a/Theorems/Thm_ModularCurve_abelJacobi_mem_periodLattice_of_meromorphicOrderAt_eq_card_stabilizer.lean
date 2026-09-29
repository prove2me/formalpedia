-- Prove2me | Theorems.Thm_ModularCurve_abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq_card_stabilizer
-- name    : ModularCurve.abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq_card_stabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/7fcbc6d5-e329-5c66-a814-2ffe04c01abe
-- title:
--   Abel's theorem for X₀(N): necessity, on H
-- statement:
--   Let $N \geq 1$, let $\Gamma_0(N) \leq \mathrm{SL}_2(\mathbb{Z})$ act on the upper half plane $\mathbb{H}$, and let $c : \mathbb{H} \to_{\mathrm{f}} \mathbb{Z}$ be a finitely supported function. Let $F : \mathbb{H} \to \mathbb{C}$ be such that: the function $z \mapsto F(\mathrm{ofComplex}\, z)$ on $\mathbb{C}$ is meromorphic at every point $\tau \in \mathbb{H}$; $F(\gamma \cdot \tau) = F(\tau)$ for every $\gamma \in \Gamma_0(N)$ and every $\tau$; for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ there is a nonzero $L \in \mathbb{C}$ with $F(\sigma \cdot \tau) \to L$ as $\operatorname{Im} \tau \to \infty$; and, for every $\tau \in \mathbb{H}$, the meromorphic order of $z \mapsto F(\mathrm{ofComplex}\, z)$ at $\tau$ equals, in $\mathbb{Z} \cup \{\infty\}$, the integer $\bigl(\mathrm{Nat.card}\,\mathrm{Stab}_{\Gamma_0(N)}(\tau) / 2\bigr) \cdot \bar{c}([\tau])$, where the division is truncated division of naturals and $\bar{c}$ is the pushforward `Finsupp.mapDomain` of $c$ along the quotient map of the orbit relation of $\Gamma_0(N)$ on $\mathbb{H}$, evaluated at the orbit of $\tau$. Then the functional $\sum_{\tau} c(\tau) \cdot \mathrm{periodAlong}\,N\,i\,\tau$ on weight-$2$ cusp forms for $\Gamma_0(N)$, where $\mathrm{periodAlong}\,N\,\tau_0\,\tau_1$ sends $f$ to $\int_0^1 f(\mathrm{segmentPath}\,\tau_0\,\tau_1\,t)\,(\tau_1 - \tau_0)\,dt$, i.e. integrates $f\,d\tau$ along the straight segment from $\tau_0$ to $\tau_1$, lies in $\mathrm{periodLattice}\,N$, the $\mathbb{Z}$-span of the functionals $\mathrm{periodAlong}\,N\,i\,(\gamma \cdot i)$ for $\gamma \in \Gamma_0(N)$.
--
--   This is the necessity direction of Abel's theorem for the compact Riemann surface $X_0(N)$, formulated entirely on $\mathbb{H}$: the hypotheses say that $F$ descends to a meromorphic function on $X_0(N)$ which is a unit at every cusp and whose divisor is $\bar{c}$, the ramification index of $\mathbb{H} \to \Gamma_0(N) \backslash \mathbb{H}$ at $\tau$ being $|\mathrm{Stab}_{\Gamma_0(N)}(\tau)|/2$. It is used by [`ModularCurve.ComplexPlaceDictionary.abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq`](thm.html#ModularCurve.ComplexPlaceDictionary.abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq), en route to identifying the divisors annihilated by the Abel–Jacobi map into the Jacobian of $X_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq_card_stabilizer.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.abelJacobi_mem_periodLattice_of_meromorphicOrderAt_eq_card_stabilizer
    {N : ℕ} [NeZero N] (c : UpperHalfPlane →₀ ℤ)
    (F : ℍ → ℂ) (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) / 2 : ℕ) *
        Finsupp.mapDomain
          (Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ)) c
          (Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ) τ) : ℤ) :
        WithTop ℤ)) :
    (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) ∈
      ModularCurve.periodLattice N := by sorry
