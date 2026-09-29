-- Prove2me | Theorems.Thm_ModularCurve_sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp_periodOf
-- name    : ModularCurve.sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp_periodOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/03ee63bc-90a9-5208-a8cb-5af1ec630c61
-- title:
--   Degree zero for a Γ-multiplicative meromorphic function
-- statement:
--   Let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ be a subgroup of finite index containing $-1$, let $F : \mathfrak{H} \to \mathbb{C}$ be a function and let $k$ be a cusp form of weight $2$ for $\Gamma$. Assume: (i) for every $\tau \in \mathfrak{H}$ the function $z \mapsto F(\mathrm{ofComplex}\,z)$ is meromorphic at the point $\tau$ of $\mathbb{C}$; (ii) for every $\gamma \in \Gamma$ and $\tau \in \mathfrak{H}$ one has $F(\gamma \cdot \tau) = \exp\bigl(2\pi i \,\mathrm{Re}\,P(\gamma)\bigr) F(\tau)$, where $P(\gamma) = (\mathrm{periodOf}\ \Gamma\ \gamma)(k)$ is the period of $k$ along the path from $i$ to $\gamma \cdot i$, i.e. the integral over $t \in [0,1]$ of the period integrand `periodIntegrandOf` of $k$ for the pair $(i, \gamma\cdot i)$; (iii) for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ the function $\tau \mapsto F(\sigma \cdot \tau)$ tends, as $\mathrm{Im}\,\tau \to \infty$, to a limit $L \ne 0$. Let $S$ be a finite subset of $\mathfrak{H}$ and $n : \mathfrak{H} \to \mathbb{Z}$ be such that the meromorphic order of $z \mapsto F(\mathrm{ofComplex}\,z)$ at each $s \in S$ is the integer $n(s)$, such that no two distinct points of $S$ are $\Gamma$-equivalent, and such that every $\tau \in \mathfrak{H}$ at which that order is non-zero lies in the $\Gamma$-orbit of some point of $S$. Then $\sum_{s \in S} n(s) / \#\mathrm{Stab}_\Gamma(s) = 0$ in $\mathbb{C}$.
--
--   This is the statement that the divisor of the single-valued untwisting function $F$ has degree zero on the modular curve $X(\Gamma)$, obtained by applying the residue theorem to $d\log F$ with the stabiliser weights $\#\mathrm{Stab}_\Gamma(s)$; the hypotheses on the cusps ensure that no contribution comes from the boundary. It is used in the construction of chains of period integrals and in the identification of sums of periods modulo the period lattice of $\Gamma$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp_periodOf.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology

set_option autoImplicit false

theorem ModularCurve.sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp_periodOf
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (F : ℍ → ℂ) (k : CuspForm (Γ) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ s ∈ S, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (s : ℂ) = (n s : WithTop ℤ))
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hcov : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) ≠ 0 →
      ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ) :
    ∑ s ∈ S, (n s : ℂ) / (Nat.card (MulAction.stabilizer (Γ) s) : ℂ)
      = 0 := by sorry
