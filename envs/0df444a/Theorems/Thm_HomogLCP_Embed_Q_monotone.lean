-- Prove2me | Theorems.Thm_HomogLCP_Embed_Q_monotone
-- name    : HomogLCP.Embed.Q_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:43:08.432992+00:00
-- url     : https://prove2.me/theorems/a78f0d89-4fec-4c42-a210-9997a0fab271
-- title:
--   Proof of Lemma 4.4, p. 11 — the union Q = F ∪ I is monotone
-- statement:
--   Let $M\in\mathbb R^{d\times d}$ satisfy $M+M^\top\succeq 0$ and $q\in\mathbb R^d$, and let $\mathcal F$ and $\mathcal I$ be the operators (4.1) and (4.7). Then
--   $$\mathcal Q=\mathcal F\cup\mathcal I$$
--   is monotone: $(v-v')^\top(u-u')\ge 0$ for all $(u,v),(u',v')\in\mathcal Q$.
--
--   This is the first half of Lemma 4.4; the second half is maximality.
--
--   **Formalization Note** The standing assumption $M+M^\top\succeq 0$ is an explicit hypothesis. The union is the union of graphs.
-- source:
--   O'Donoghue, Operator splitting for a homogeneous embedding of the linear complementarity problem, arXiv:2004.02177v4, p. 11, proof of Lemma 4.4, first paragraph

import Mathlib
import Definitions.Def_HomogLCP_Embed_MonotoneOp
import Definitions.Def_HomogLCP_Embed_Setting

namespace HomogLCP.Embed

open Matrix

/-- Proof of Lemma 4.4, p. 11, first paragraph: `𝒬 = ℱ ∪ ℐ` is monotone. -/
theorem Q_monotone {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → ℝ)
    (hM : (M + Mᵀ).PosSemidef) :
    IsMonotoneOp (embQ M q) := by sorry

end HomogLCP.Embed
