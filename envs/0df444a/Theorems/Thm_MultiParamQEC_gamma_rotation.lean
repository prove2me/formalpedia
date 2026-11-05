-- Prove2me | Theorems.Thm_MultiParamQEC_gamma_rotation
-- name    : MultiParamQEC.gamma_rotation
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:39:57.296392+00:00
-- url     : https://prove2.me/theorems/086df48c-ae23-4fe7-9bd9-2318e7ab3d4c
-- title:
--   Sec. 4.2.3 — rotating the reference basis makes $\Gamma\sqrt{W^{-1}}\ge0$ without changing feasibility or cost
-- statement:
--   Let $W$ be real positive definite with positive semidefinite square root $\sqrt{W^{-1}}$ of $W^{-1}$, and let $(G^R,B,\nu)$ be feasible for (25) ($G^R_i,B_i$ Hermitian, $Q\ge0$) with $\Gamma$ invertible. Then there is a real orthogonal $P\times P$ matrix $O$ such that, rotating the reference basis by $\mathbb 1\oplus O$ ($G^R_i\mapsto(\mathbb 1\oplus O)G^R_i(\mathbb 1\oplus O)^T$, likewise $B_i$, same $\nu$):
--
--   1. the rotated point is again feasible;
--   2. its $\Gamma$ is $O\Gamma$;
--   3. $O\Gamma\sqrt{W^{-1}}\ge0$;
--   4. $\mathrm{Tr}\big(W((O\Gamma)^TO\Gamma)^{-1}\big)=\mathrm{Tr}\big(W(\Gamma^T\Gamma)^{-1}\big)$.
--
--   So one may assume $\Gamma\sqrt{W^{-1}}\ge0$ in (26) without loss of generality.
--
--   Differences from the source:
--   - encoding: √(W⁻¹) → an argument Rw with Rw.PosSemidef and Rw * Rw = W⁻¹; reason: the positive semidefinite square root is unique, so this is the source's matrix
--   - encoding: reference space H_R = span{|0⟩,…,|P⟩}, indices 0..P; parameter indices 1..P → Fin (P+1) with index 0 the input state; i ∈ 1..P is Fin.succ i for i : Fin P; Q indexed by Fin (P+1) × Fin d, reference first; reason: Lean convention; same instances
--   - encoding: an orthonormal matrix O → a real matrix O with Oᵀ * O = 1; reason: a real orthogonal matrix; same instances
-- source:
--   Górecki–Zhou–Jiang–Demkowicz-Dobrzański, Optimal probes and error-correction schemes in multi-parameter quantum metrology, arXiv:1901.00896v4, Sec. 4.2.3, first paragraph, p.9

import Mathlib
import Definitions.Def_MultiParamQEC_SDP

open scoped ComplexOrder Matrix Kronecker

namespace MultiParamQEC

/-- **Rotating the reference basis makes `Γ√(W⁻¹)` positive semidefinite**
(Górecki–Zhou–Jiang–Demkowicz-Dobrzański, arXiv:1901.00896v4, Sec. 4.2.3, first paragraph, p.9:
"for any full rank matrix `Γ`, the polar decomposition theorem implies that there always exists an
orthonormal matrix `O` such that `OΓ√(W⁻¹) ≥ 0`", and "such a rotation cannot change the
non-negativity of `Q` and at the same time it does not affect the figure of merit
`Tr(W(ΓᵀΓ)⁻¹)`").

For every feasible `(G^R, B, ν)` of (25) with `Γ` invertible, there is a real orthogonal `O` such
that the generators and the `B_i` rotated by `1 ⊕ O` on the reference space are again feasible
(with the same `ν`), the rotated `Γ` is `OΓ`, `OΓ√(W⁻¹)` is (symmetric) positive semidefinite, and
`Tr(W((OΓ)ᵀOΓ)⁻¹) = Tr(W(ΓᵀΓ)⁻¹)`. Here `Rw` is the positive semidefinite square root of `W⁻¹`. -/
theorem gamma_rotation {d P m r : ℕ} (G : Fin P → Matrix (Fin d) (Fin d) ℂ)
    (S : Fin m → Matrix (Fin d) (Fin d) ℂ) (R : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (W : Matrix (Fin P) (Fin P) ℝ) (hW : W.PosDef)
    (Rw : Matrix (Fin P) (Fin P) ℝ) (hRw : Rw.PosSemidef) (hRw2 : Rw * Rw = W⁻¹)
    (GR : Fin P → Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ)
    (B : Fin r → Matrix (Fin (P + 1)) (Fin (P + 1)) ℂ) (ν : Fin m → ℝ)
    (hfeas : IsCodeFeasible G S R GR B ν) (hΓ : (gammaMatrix GR).det ≠ 0) :
    ∃ O : Matrix (Fin P) (Fin P) ℝ, Oᵀ * O = 1 ∧
      IsCodeFeasible G S R (fun i => rotateRef O (GR i)) (fun i => rotateRef O (B i)) ν ∧
      gammaMatrix (fun i => rotateRef O (GR i)) = O * gammaMatrix GR ∧
      (O * gammaMatrix GR * Rw).PosSemidef ∧
      (W * ((O * gammaMatrix GR)ᵀ * (O * gammaMatrix GR))⁻¹).trace =
        (W * ((gammaMatrix GR)ᵀ * gammaMatrix GR)⁻¹).trace := by sorry

end MultiParamQEC
