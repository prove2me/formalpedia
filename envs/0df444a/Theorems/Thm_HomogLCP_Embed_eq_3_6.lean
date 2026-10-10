-- Prove2me | Theorems.Thm_HomogLCP_Embed_eq_3_6
-- name    : HomogLCP.Embed.eq_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:12.168763+00:00
-- url     : https://prove2.me/theorems/c743654d-8cf4-4dbf-9384-ebe4b3b9bae7
-- title:
--   (3.6), p. 5 — for monotone M, zᵀMz = 0 ⇔ (M + Mᵀ)z = 0
-- statement:
--   Let $M\in\mathbb R^{d\times d}$ be monotone, i.e. $M+M^\top\succeq 0$ (3.4). Then for every $z\in\mathbb R^d$,
--   $$z^\top Mz=0\iff (M+M^\top)z=0 .$$
--
--   This is the algebraic fact behind every monotonicity argument of §4: it converts the scalar condition $z^\top Mz=0$ defining $\operatorname{dom}\mathcal I$ into the linear identity $Mz=-M^\top z$.
--
--   **Formalization Note** "$M$ is monotone" is the hypothesis `(M + Mᵀ).PosSemidef`; $M$ is not assumed symmetric.
-- source:
--   O'Donoghue, Operator splitting for a homogeneous embedding of the linear complementarity problem, arXiv:2004.02177v4, p. 5, (3.6)

import Mathlib

namespace HomogLCP.Embed

open Matrix

/-- (3.6), p. 5: for monotone `M` (`M + Mᵀ ⪰ 0`), `zᵀMz = 0 ⇔ (M + Mᵀ)z = 0`. -/
theorem eq_3_6 {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (hM : (M + Mᵀ).PosSemidef) :
    ∀ z : Fin d → ℝ, z ⬝ᵥ (M *ᵥ z) = 0 ↔ (M + Mᵀ) *ᵥ z = 0 := by sorry

end HomogLCP.Embed
