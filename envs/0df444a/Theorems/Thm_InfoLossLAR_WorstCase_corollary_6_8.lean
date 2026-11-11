-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_corollary_6_8
-- name    : InfoLossLAR.WorstCase.corollary_6_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:03:54.07485+00:00
-- url     : https://prove2.me/theorems/0c7a9096-7c93-4ffa-9705-03ebd9e99604
-- title:
--   Corollary 6.8 — tree-incidence transport: $Q=T^{-1}\bar D_{\mathscr T}\bar R$ integral with $\det Q=\pm\det R_{\mathrm{edge}}$
-- statement:
--   Let $q$ be an odd prime, $d\ge q$ and $T$ the matrix of Definition 6.3. Let $\mathscr T$ be any oriented spanning tree on $\{1,\dots,d\}$, $R_{\mathrm{edge}}\in\mathbb Z^{(d-1)\times(d-1)}$, and $v\in\mathbb Z^d$ with $\mathbf 1^\top v=q$. Define
--   $$\bar D_{\mathscr T}=[D_{\mathscr T}\mid v],\qquad \bar R=\operatorname{diag}(R_{\mathrm{edge}},1),\qquad D_{\mathbf T}=\bar D_{\mathscr T}\bar R\in\mathbb Z^{d\times d}.$$
--   Let $z_0\in\mathbb Z^d$ with $\mathbf 1^\top z_0\equiv0\pmod q$, and set $Q=T^{-1}D_{\mathbf T}$, $\beta=T^{-1}z_0$. Then $|\det\bar D_{\mathscr T}|=q$, $D_{\mathbf T}\mathbb Z^d\subseteq\mathcal L(T)$ and $z_0\in\mathcal L(T)$; consequently $Q\in\mathbb Z^{d\times d}$ and $\beta\in\mathbb Z^d$, with
--   $$\det D_{\mathbf T}=\pm q\det R_{\mathrm{edge}},\qquad \det Q=\frac{\det\bar D_{\mathscr T}\det\bar R}{\det T}=\pm\det R_{\mathrm{edge}} .$$
--   Every $x\in\mathbb Z^d$ gives $w=\bar D_{\mathscr T}\bar Rx+z_0\in\mathcal L(T)$ and $w\bmod q\in H_0$. If $\det R_{\mathrm{edge}}\not\equiv0\pmod q$, then $Q\bmod q\in\mathrm{GL}_d(\mathbb F_q)$.
--
--   Differences from the source:
--   - encoding: the column order of $\bar D_{\mathscr T}$ (edges, then $v$) → an arbitrary bijection $\sigma$ from (edges $\sqcup$ one extra column) to $\{1,\dots,d\}$, with $\bar R$ reindexed by the same $\sigma$ on rows and columns; reason: the paper does not order the edges; $D_{\mathbf T}$ is the paper's matrix with columns permuted, and every clause is invariant
--   - encoding: $R_{\mathrm{edge}}\in\mathbb Z^{(d-1)\times(d-1)}$ → indexed by the edge set; reason: its rows and columns are the edge coordinates
--   - encoding: "$Q\in\mathbb Z^{d\times d}$, $\beta\in\mathbb Z^d$" → there are integer $Q_{\mathbb Z},\beta_{\mathbb Z}$ whose casts are the rational $Q,\beta$, and invertibility mod $q$ is stated for $Q_{\mathbb Z}$; reason: $T^{-1}$ is taken over $\mathbb Q$
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 29, Corollary 6.8

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_Rounding
import Definitions.Def_InfoLossLAR_WorstCase_FixedT

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

/-- Corollary 6.8 (General tree-incidence transport), p. 29. `q` an odd prime, `d ≥ q`, `T` of
Definition 6.3, `𝒯` any oriented spanning tree on `Fin d`, `R_edge ∈ ℤ^{(d−1)×(d−1)}` (indexed
by the edges), `v ∈ ℤ^d` with `1ᵀv = q`, `z_0 ∈ ℤ^d` with `1ᵀz_0 ≡ 0 (mod q)`; the `d` columns
are ordered by `σ` (edges, then the extra column). With `D̄_𝒯 = [D_𝒯 | v]`,
`R̄ = diag(R_edge, 1)`, `D_T = D̄_𝒯 R̄`, `Q = T^{-1} D_T` and `β = T^{-1} z_0` (over `ℚ`):
`|det D̄_𝒯| = q`, `D_T ℤ^d ⊆ L(T)`, `z_0 ∈ L(T)`, `Q` and `β` are integral,
`det D_T = ±q det R_edge`, `det Q = det D̄_𝒯 det R̄ / det T = ±det R_edge`, every `x ∈ ℤ^d`
gives `w = D̄_𝒯 R̄ x + z_0 ∈ L(T)` with `w mod q ∈ H_0`, and if `det R_edge ≢ 0 (mod q)` then
`Q mod q ∈ GL_d(𝔽_q)`. -/
theorem corollary_6_8 (q d : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hdq : q ≤ d)
    (𝒯 : OrientedTree d) (Redge : Matrix 𝒯.G.edgeSet 𝒯.G.edgeSet ℤ)
    (v : Fin d → ℤ) (hv : ∑ i, v i = (q : ℤ))
    (z₀ : Fin d → ℤ) (hz₀ : (q : ℤ) ∣ ∑ i, z₀ i)
    (σ : 𝒯.G.edgeSet ⊕ Unit ≃ Fin d) :
    let Dbar : Matrix (Fin d) (Fin d) ℤ := (𝒯.extended v).submatrix id σ.symm
    let Rbar : Matrix (Fin d) (Fin d) ℤ :=
      (Matrix.fromBlocks Redge 0 0 (1 : Matrix Unit Unit ℤ)).submatrix σ.symm σ.symm
    let DT : Matrix (Fin d) (Fin d) ℤ := Dbar * Rbar
    let Q : Matrix (Fin d) (Fin d) ℚ := TinvQ q d * DT.map (Int.cast : ℤ → ℚ)
    let β : Fin d → ℚ := (TinvQ q d).mulVec (fun i => (z₀ i : ℚ))
    |Dbar.det| = (q : ℤ) ∧
    (∀ x : Fin d → ℤ, DT.mulVec x ∈ imageLattice (TDef63 q d)) ∧
    z₀ ∈ imageLattice (TDef63 q d) ∧
    (DT.det = (q : ℤ) * Redge.det ∨ DT.det = -((q : ℤ) * Redge.det)) ∧
    Q.det = ((Dbar.det * Rbar.det : ℤ) : ℚ) / (((TDef63 q d).det : ℤ) : ℚ) ∧
    (Q.det = (Redge.det : ℚ) ∨ Q.det = -(Redge.det : ℚ)) ∧
    (∃ Qz : Matrix (Fin d) (Fin d) ℤ, Qz.map (Int.cast : ℤ → ℚ) = Q ∧
      (¬ (q : ℤ) ∣ Redge.det → IsUnit (matModq q Qz).det)) ∧
    (∃ βz : Fin d → ℤ, (fun i => (βz i : ℚ)) = β) ∧
    (∀ x : Fin d → ℤ, DT.mulVec x + z₀ ∈ imageLattice (TDef63 q d) ∧
      modq q (DT.mulVec x + z₀) ∈ H0 q d) := by sorry

end InfoLossLAR.WorstCase
