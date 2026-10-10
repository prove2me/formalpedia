-- Prove2me | Theorems.Thm_HomogLCP_Embed_lemma_4_3
-- name    : HomogLCP.Embed.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:42:53.338193+00:00
-- url     : https://prove2.me/theorems/596896f2-a219-4b5c-b765-26a1914b925d
-- title:
--   Lemma 4.3, pp. 9–10 — the infeasibility operator I is monotone
-- statement:
--   Let $M\in\mathbb R^{d\times d}$ satisfy $M+M^\top\succeq 0$ and $q\in\mathbb R^d$. The set-valued operator
--   $$\mathcal I(z,\tau)=\left\{\begin{bmatrix} Mz\\ \kappa\end{bmatrix}\ \middle|\ \kappa\le -z^\top q\right\},\qquad \operatorname{dom}\mathcal I=\{(z,0)\mid z^\top Mz=0\},$$
--   of (4.7) is monotone.
--
--   Together with Lemma 4.1 it reduces the monotonicity of $\mathcal Q=\mathcal F\cup\mathcal I$ to the cross terms between $\operatorname{dom}\mathcal F$ and $\operatorname{dom}\mathcal I$.
--
--   **Formalization Note** The standing assumption $M+M^\top\succeq 0$ is an explicit hypothesis. $\mathcal I$ is used exactly as (4.7) defines it, including the domain condition $z^\top Mz=0$.
-- source:
--   O'Donoghue, Operator splitting for a homogeneous embedding of the linear complementarity problem, arXiv:2004.02177v4, pp. 9–10, Lemma 4.3

import Mathlib
import Definitions.Def_HomogLCP_Embed_MonotoneOp
import Definitions.Def_HomogLCP_Embed_Setting

namespace HomogLCP.Embed

open Matrix

/-- Lemma 4.3, pp. 9–10: the operator `ℐ` is monotone. -/
theorem lemma_4_3 {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → ℝ)
    (hM : (M + Mᵀ).PosSemidef) :
    IsMonotoneOp (embI M q) := by sorry

end HomogLCP.Embed
