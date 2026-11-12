-- Prove2me | Theorems.Thm_HyperCheeger_eq_7
-- name    : HyperCheeger.eq_7
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:03:11.816612+00:00
-- url     : https://prove2.me/theorems/e1765bbe-4909-4e79-84a3-0ef858097d61
-- title:
--   Eq. (7) — Rayleigh characterization of $\nu_2(H)$
-- statement:
--   Let $H$ be a hypergraph on at least two vertices, and define $\psi_1,\hat\psi_1\in\mathbb R^{V_H}$ by $\psi_1(u)=\sqrt{d_H(u)}$ and $\hat\psi_1(u)=d_H(u)$. Then $\psi_1$ is an eigenvector of $\mathcal L_H$ for the eigenvalue $0$, and
--
--   $$\nu_2(H)=\min_{x\perp\psi_1}\frac{x^{T}\mathcal L_Hx}{x^{T}x}=\min_{y\perp\hat\psi_1}\frac{y^{T}L_Hy}{y^{T}D_Hy},$$
--
--   where both minima range over nonzero vectors and are attained. This is the variational form of $\nu_2$ used to compare it with cut quantities.
--
--   Differences from the source:
--   - encoding: min over x ⊥ ψ₁ and y ⊥ ψ̂₁ → IsLeast over nonzero vectors in those complements; reason: a Rayleigh quotient needs a nonzero vector, and IsLeast states that the minimum is attained
--   - encoding: ψ₁ is an eigenvector for the eigenvalue 0 → 𝓛_H ψ₁ = 0; reason: ψ₁ = 0 when all weights vanish, which w_H : E_H → [0,∞) allows; otherwise ψ₁ ≠ 0 and the two say the same
--   - encoding: D_H^{-1/2} and yᵀL_H y / yᵀD_H y are undefined with zero degrees → the entry 1/√0 is 0 and the quotient 0/0 is 0; reason: w_H may vanish; instances with all degrees positive are unchanged
--   - encoding: a set of n vertices, with ν₂ and a proper nonempty subset implicitly available → a finite type V with 2 ≤ card V; reason: ν₂ needs two eigenvalues and the minimum over ∅ ⊊ S ⊊ V needs a set S; connectedness already excludes card V = 1
-- source:
--   Kamal, Bagchi, A Cheeger Inequality for Hypergraphs and Its Applications, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), eq. (7), p.8

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph_nu2

open scoped Matrix

namespace HyperCheeger

/-- **Eq. (7)**: with `ψ₁(u) = √(d_H(u))` and `ψ̂₁(u) = d_H(u)`, `ψ₁` is an eigenvector of `𝓛_H` for
the eigenvalue `0`, and
`ν₂(H) = min_{x ⊥ ψ₁} xᵀ𝓛_H x / xᵀx = min_{y ⊥ ψ̂₁} yᵀL_H y / yᵀD_H y`.

Kamal, Bagchi, *A Cheeger Inequality for Hypergraphs and Its Applications*, STOC 2027 submission,
arXiv:2609.16286 (manuscript sha256 e0942b89…), eq. (7), p.8.

**Formalization Note.** The minima range over nonzero vectors, as a Rayleigh quotient requires, and
`IsLeast` makes attainment part of the claim. When all degrees vanish `ψ₁ = 0`, and "eigenvector" is read
as the identity `𝓛_H ψ₁ = 0`. A `y` supported on zero-degree vertices gives `0/0 = 0`, in which case
`ν₂(H) = 0`. -/
theorem eq_7 {V : Type} [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V) (H : Hypergraph V) :
    H.normLap *ᵥ (fun u => Real.sqrt (H.degree u)) = 0 ∧
    IsLeast {r : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ x ⬝ᵥ (fun u => Real.sqrt (H.degree u)) = 0 ∧
        r = (x ⬝ᵥ (H.normLap *ᵥ x)) / (x ⬝ᵥ x)} H.nu2 ∧
    IsLeast {r : ℝ | ∃ y : V → ℝ, y ≠ 0 ∧ y ⬝ᵥ H.degree = 0 ∧
        r = (y ⬝ᵥ (H.lap *ᵥ y)) / (y ⬝ᵥ (H.degMat *ᵥ y))} H.nu2 := by sorry

end HyperCheeger
