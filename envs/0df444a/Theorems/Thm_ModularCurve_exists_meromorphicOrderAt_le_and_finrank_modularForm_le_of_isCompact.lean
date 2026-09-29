-- Prove2me | Theorems.Thm_ModularCurve_exists_meromorphicOrderAt_le_and_finrank_modularForm_le_of_isCompact
-- name    : ModularCurve.exists_meromorphicOrderAt_le_and_finrank_modularForm_le_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/39e29568-d339-5287-bea6-aac864b475ec
-- title:
--   Linear bounds on vanishing orders and dim M_k(Γ) for cocompact Γ
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ all of whose elements have determinant $1$ (the `Γ.HasDetOne` instance), carrying the discrete subspace topology, and assume $\Gamma$ acts cocompactly on the upper half-plane $\mathbb{H}$ in the following sense: there is a compact set $K \subseteq \mathbb{H}$ such that every $\tau \in \mathbb{H}$ has some $\gamma \in \Gamma$ with $\gamma \cdot \tau \in K$. The assertion is the existence of a single natural number $C$, depending only on $\Gamma$, such that for every integer weight $k \ge 0$ three statements hold simultaneously. First, for every modular form $f$ of weight $k$ for $\Gamma$ whose underlying function $\mathbb{H} \to \mathbb{C}$ is not identically zero, and every $\tau \in \mathbb{H}$, the meromorphic order at the point $\tau \in \mathbb{C}$ of the function $z \mapsto f(\mathrm{ofComplex}\, z)$ on $\mathbb{C}$ — the extension of $f$ to the plane obtained by transporting along `ofComplex`, which is the identity on the upper half-plane — is at most $C k$ as an element of $\mathbb{Z} \cup \{\infty\}$; in particular this order is finite. Second, the $\mathbb{C}$-vector space `ModularForm Γ k` is finite-dimensional. Third, its rank over $\mathbb{C}$ is at most $C \cdot k + 1$, the weight being read as a natural number via `Int.toNat`.
--
--   This is the standard linear growth estimate for holomorphic automorphic forms on a compact quotient: orders of vanishing of a non-zero weight-$k$ form are $O(k)$ and hence $\dim_{\mathbb{C}} M_k(\Gamma) = O(k)$, with a constant uniform in $k$. It feeds into [`ModularCurve.isCurveOver_automorphicField_of_isCompact`](thm.html#ModularCurve.isCurveOver_automorphicField_of_isCompact), where the resulting growth of the graded ring of forms is used to bound the transcendence degree of the field of automorphic functions attached to $\Gamma$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_meromorphicOrderAt_le_and_finrank_modularForm_le_of_isCompact.lean

import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.exists_meromorphicOrderAt_le_and_finrank_modularForm_le_of_isCompact
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    [hdisc : DiscreteTopology ↥Γ]
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K) :
    ∃ C : ℕ, ∀ k : ℤ, 0 ≤ k →
      (∀ f : ModularForm Γ k, (f : ℍ → ℂ) ≠ 0 → ∀ τ : ℍ,
        meromorphicOrderAt (fun z : ℂ => f (ofComplex z)) (τ : ℂ) ≤ (((C : ℤ) * k : ℤ) : WithTop ℤ)) ∧
      FiniteDimensional ℂ (ModularForm Γ k) ∧
      Module.finrank ℂ (ModularForm Γ k) ≤ C * k.toNat + 1 := by sorry
