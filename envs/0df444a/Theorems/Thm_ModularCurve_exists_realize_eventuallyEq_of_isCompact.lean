-- Prove2me | Theorems.Thm_ModularCurve_exists_realize_eventuallyEq_of_isCompact
-- name    : ModularCurve.exists_realize_eventuallyEq_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/0ed563e9-eb19-5e5c-a026-72d2130c94b8
-- title:
--   Every Γ-invariant meromorphic function on H is a ratio of forms
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ all of whose elements have determinant $1$, carrying the discrete topology. Assume: (i) cocompactness in the form that there is a compact $K \subseteq \mathbb{H}$ meeting every $\Gamma$-orbit, i.e. for each $\tau \in \mathbb{H}$ some $\gamma \in \Gamma$ has $\gamma \cdot \tau \in K$; (ii) no point $c$ of the one-point compactification of $\mathbb{R}$ satisfies `IsCusp c Γ`; (iii) zeros can be prescribed: for every finite set $S \subseteq \mathbb{H}$ and every $n : \mathbb{H} \to \mathbb{N}$ there are an even weight $k \ge 4$ and a modular form $P$ of weight $k$ for $\Gamma$ with $P \ne 0$ as a function and $\operatorname{ord}_\tau P \ge n(\tau)$ for all $\tau \in S$, the order being the meromorphic order at $\tau$ of $P$ read as a function of a complex variable. Let $f : \mathbb{H} \to \mathbb{C}$ be meromorphic at every point of $\mathbb{H}$ and satisfy, for each $\gamma \in \Gamma$ and each $\tau$, $f(\gamma \cdot z) = f(z)$ for $z$ in a punctured neighbourhood of $\tau$. Then there is an element $x$ of [`ModularCurve.automorphicField Γ`](def/ModularCurve_AutomorphicField.html#L150) — the subfield of the fraction field of the $\mathbb{C}$-algebra of holomorphic functions $\mathbb{H} \to \mathbb{C}$ consisting of the classes $g/h$ with $g,h$ modular forms of one common weight for $\Gamma$ and $h \ne 0$ — whose realisation as the quotient of a chosen numerator and denominator agrees with $f$ on a punctured neighbourhood of every $\tau \in \mathbb{H}$.
--
--   This is the surjectivity half of the classical identification, for a discrete cocompact cusp-free subgroup, of the field of automorphic functions (ratios of modular forms of equal weight) with the field of all $\Gamma$-invariant meromorphic functions on the upper half plane. It feeds the construction [`ModularCurve.UniformizedHeckeCurve.exists_of_isCompact_of_discrete`](thm.html#ModularCurve.UniformizedHeckeCurve.exists_of_isCompact_of_discrete), where the quotient $\mathbb{H}/\Gamma$ is presented as an algebraic curve with its function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_realize_eventuallyEq_of_isCompact.lean

import Definitions.Def_ModularCurve_AutomorphicField
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.exists_realize_eventuallyEq_of_isCompact
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    [hdisc : DiscreteTopology ↥Γ]
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K)
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ)
    (hample : ∀ (S : Finset ℍ) (n : ℍ → ℕ),
      ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ P : ModularForm Γ k, (P : ℍ → ℂ) ≠ 0 ∧
        ∀ τ ∈ S, ((n τ : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun z : ℂ => P (ofComplex z)) (τ : ℂ))
    (f : ℍ → ℂ) (hf : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => f (ofComplex z)) (τ : ℂ))
    (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ, f (γ • z) = f z) :
    ∃ x : ↥(ModularCurve.automorphicField Γ),
      ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ, ModularCurve.automorphicField.realize x z = f z := by sorry
