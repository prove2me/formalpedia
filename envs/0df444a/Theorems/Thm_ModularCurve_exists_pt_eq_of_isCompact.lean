-- Prove2me | Theorems.Thm_ModularCurve_exists_pt_eq_of_isCompact
-- name    : ModularCurve.exists_pt_eq_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/87b07ee0-b5d8-5833-89e6-b47326beac7c
-- title:
--   Every place of a cocompact automorphic function field is a point
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ all of whose elements have determinant $1$, carrying the discrete topology, and assume $\Gamma$ acts cocompactly on the upper half plane in the sense that there is a compact set $K \subseteq \mathbb{H}$ such that every $\tau \in \mathbb{H}$ has some $\gamma \in \Gamma$ with $\gamma \cdot \tau \in K$. Let $F =$ [`ModularCurve.automorphicField`](def/ModularCurve_AutomorphicField.html#L150) $\Gamma$ be the subfield of the fraction field of the ring of holomorphic functions on $\mathbb{H}$ consisting of the quotients $g/h$ of two modular forms of some common weight $k$ for $\Gamma$ with $h \neq 0$, and assume $F$ is a curve over $\mathbb{C}$: every nonzero element of $F$ has a divisor of degree $0$ recording its order at each place, every place has residue field of finite dimension over $\mathbb{C}$, and $\Omega_{F/\mathbb{C}}$ is free of rank one over $F$. Here a place of $F/\mathbb{C}$ is a valuation subring of $F$ containing the image of $\mathbb{C}$, distinct from $F$, and a principal ideal ring. Let $\mathrm{pt} : \mathbb{H} \to \{\text{places of } F/\mathbb{C}\}$ be any map such that for all $\tau$ and all $x \in F$, the element $x$ lies in the valuation subring of $\mathrm{pt}(\tau)$ precisely when $z \mapsto \|\mathrm{realize}(x)(z)\|$ is bounded above along the punctured neighbourhood filter of $\tau$, where $\mathrm{realize}(x)$ is the meromorphic function on $\mathbb{H}$ presenting $x$ as a quotient of holomorphic functions. Then every place $P$ of $F/\mathbb{C}$ is of the form $\mathrm{pt}(\tau)$ for some $\tau \in \mathbb{H}$.
--
--   This is the statement that for a cocompact discrete group the quotient $\Gamma \backslash \mathbb{H}$ has no missing points or cusps, read on the function field: the map from points of $\mathbb{H}$ to places of the automorphic function field is surjective. It supplies the surjectivity clause in the construction of the uniformized Hecke curve attached to such a $\Gamma$, [`ModularCurve.UniformizedHeckeCurve.exists_of_isCompact_of_discrete`](thm.html#ModularCurve.UniformizedHeckeCurve.exists_of_isCompact_of_discrete).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_pt_eq_of_isCompact.lean

import Definitions.Def_ModularCurve_AutomorphicField
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.exists_pt_eq_of_isCompact
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    [hdisc : DiscreteTopology ↥Γ]
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K)
    [AlgebraicCurve.IsCurveOver ℂ ↥(ModularCurve.automorphicField Γ)]
    (pt : ℍ → AlgebraicCurve.Place ℂ ↥(ModularCurve.automorphicField Γ))
    (hpt : ∀ (τ : ℍ) (x : ↥(ModularCurve.automorphicField Γ)), x ∈ (pt τ).toValuationSubring ↔
      Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ) (fun z : ℍ => ‖ModularCurve.automorphicField.realize x z‖))
    (P : AlgebraicCurve.Place ℂ ↥(ModularCurve.automorphicField Γ)) :
    ∃ τ : ℍ, pt τ = P := by sorry
