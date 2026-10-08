-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondI_dihedral_angle_bound
-- name    : NonuniformKuramoto.CondI.dihedral_angle_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:33.178984+00:00
-- url     : https://prove2.me/theorems/29115e1a-99a8-4612-90f1-b1ed67d45a84
-- title:
--   Proof of Theorem V.1, p. 18 — $\|\delta\|\ge\|\delta_\perp\|\ge\|\delta\|\cos(\angle(D\mathbf 1_n,\mathbf 1_n))$
-- statement:
--   Let $D_1,\dots,D_n>0$ and let $\delta\in\mathbb R^n$ satisfy $\delta^TD\mathbf 1_n=\sum_iD_i\delta_i=0$. Let $\delta_\perp=\delta-\frac{\mathbf 1_n^T\delta}{n}\mathbf 1_n$ be the orthogonal projection of $\delta$ onto the subspace orthogonal to $\mathbf 1_n$. Then
--
--   $$\|\delta\|_2\ \ge\ \|\delta_\perp\|_2\ \ge\ \|\delta\|_2\cos(\angle(D\mathbf 1_n,\mathbf 1_n)),$$
--
--   where $\cos(\angle(D\mathbf 1_n,\mathbf 1_n))=\sum_iD_i/(\sqrt n\,\|D\|_2)$.
--
--   The bound converts the decay of the disagreement measured orthogonally to $\mathbf 1_n$ into decay of the weighted disagreement vector, producing the factor $\cos(\angle(D\mathbf 1,\mathbf 1))^2$ in the rate (19).
--
--   **Formalization Note** The page also says "$\delta\notin\operatorname{span}(\mathbf 1_n)$", which fails for $\delta=0$ and is not part of the claim.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 18, proof of Theorem V.1, last sentence

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_CondI_Constants

namespace NonuniformKuramoto.CondI

/-- Proof of Theorem V.1, p. 18: for `δ` with `δᵀ D 1_n = 0` and `δ_⊥ = δ − (1_nᵀ δ / n) 1_n` its
orthogonal projection onto the complement of `1_n`, `‖δ‖ ≥ ‖δ_⊥‖ ≥ ‖δ‖ cos(∠(D1_n, 1_n))`. -/
theorem dihedral_angle_bound {n : ℕ} (D : Fin n → ℝ) (hD : ∀ i, 0 < D i)
    (δ : Fin n → ℝ) (hδ : ∑ i, D i * δ i = 0) :
    norm2 (fun i => δ i - (∑ j, δ j) / n) ≤ norm2 δ ∧
    norm2 δ * cosAngleD D ≤ norm2 (fun i => δ i - (∑ j, δ j) / n) := by sorry

end NonuniformKuramoto.CondI
