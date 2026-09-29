-- Prove2me | Theorems.Thm_ModularCurve_exists_placeDictionary_automorphicField_of_discreteTopology
-- name    : ModularCurve.exists_placeDictionary_automorphicField_of_discreteTopology
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/59e9bba6-795a-5905-b0ac-dce3b04a4c05
-- title:
--   Points of H as places of the automorphic function field
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb R)$ all of whose elements have determinant one (`Γ.HasDetOne`), with $-1 \in \Gamma$ and with the subspace topology on $\Gamma$ discrete. Assume two hypotheses on modular forms for $\Gamma$: (separation) for all $\tau,\sigma \in \mathbb H$ lying in distinct $\Gamma$-orbits there are an even weight $k \ge 4$ and forms $g,h \in M_k(\Gamma)$ with $g(\tau)h(\sigma) \ne g(\sigma)h(\tau)$; (local normalisation) for every $\tau \in \mathbb H$ there are an even weight $k \ge 4$ and $g,h \in M_k(\Gamma)$ with $h(\tau) \ne 0$ such that the meromorphic order at $\tau$ of $z \mapsto g/h$, transported to $\mathbb C$ along `ofComplex`, equals $e_\tau := \#\mathrm{Stab}_\Gamma(\tau)/2$ (natural-number division). Write $\mathcal K(\Gamma) =$ `automorphicField Γ` for the subfield of the fraction field of the algebra of $\mathbb C$-differentiable functions $\mathbb H \to \mathbb C$ consisting of the quotients $g/h$ of modular forms of a common weight with $h \ne 0$, and `automorphicField.realize x` for the function $\mathbb H \to \mathbb C$ obtained from a representing quotient. Then there is a map $\mathrm{pt}$ from $\mathbb H$ to the places of $\mathcal K(\Gamma)$ over $\mathbb C$ — valuation subrings containing $\mathbb C$, proper, and principal ideal rings — such that for every $\tau$: $x$ lies in the valuation subring of $\mathrm{pt}(\tau)$ iff $\|\mathrm{realize}\,x\|$ is bounded above on a punctured neighbourhood of $\tau$; for $x \ne 0$ the meromorphic order at $\tau$ of $\mathrm{realize}\,x$ equals $e_\tau \cdot \mathrm{ord}_{\mathrm{pt}(\tau)}(x)$; and $\mathrm{pt}(\tau) = \mathrm{pt}(\tau')$ iff $\tau' \in \Gamma\tau$.
--
--   This is the place dictionary attaching to each point of the upper half plane a place of the field of automorphic functions of $\Gamma$, with regularity detected by local boundedness and with ramification index $e_\tau = \tfrac12\#\mathrm{Stab}_\Gamma(\tau)$; no cocompactness is required. It supplies three of the clauses of a uniformised Hecke curve and is used by [`ModularCurve.UniformizedHeckeCurve.exists_of_isCompact_of_discrete`](thm.html#ModularCurve.UniformizedHeckeCurve.exists_of_isCompact_of_discrete).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_placeDictionary_automorphicField_of_discreteTopology.lean

import Definitions.Def_ModularCurve_AutomorphicField
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.exists_placeDictionary_automorphicField_of_discreteTopology
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    (hneg : -1 ∈ Γ)
    [hdisc : DiscreteTopology ↥Γ]
    (hsep : ∀ τ σ : ℍ, (∀ γ ∈ Γ, γ • τ ≠ σ) →
      ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ g h : ModularForm Γ k, g τ * h σ ≠ g σ * h τ)
    (hloc : ∀ τ : ℍ, ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ g h : ModularForm Γ k, h τ ≠ 0 ∧
      meromorphicOrderAt (fun z : ℂ => g (ofComplex z) / h (ofComplex z)) (τ : ℂ) =
        (((Nat.card (MulAction.stabilizer Γ τ) / 2 : ℕ) : ℤ) : WithTop ℤ)) :
    ∃ pt : ℍ → AlgebraicCurve.Place ℂ ↥(ModularCurve.automorphicField Γ),
      (∀ (τ : ℍ) (x : ↥(ModularCurve.automorphicField Γ)), x ∈ (pt τ).toValuationSubring ↔
        Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
          (fun z : ℍ => ‖ModularCurve.automorphicField.realize x z‖)) ∧
      (∀ (τ : ℍ) (x : ↥(ModularCurve.automorphicField Γ)), x ≠ 0 →
        meromorphicOrderAt (fun z : ℂ => ModularCurve.automorphicField.realize x (ofComplex z)) (τ : ℂ) =
          ((((Nat.card (MulAction.stabilizer Γ τ) / 2 : ℕ) : ℤ) * (pt τ).ord x : ℤ) : WithTop ℤ)) ∧
      (∀ τ τ' : ℍ, pt τ = pt τ' ↔ ∃ γ ∈ Γ, γ • τ = τ') := by sorry
