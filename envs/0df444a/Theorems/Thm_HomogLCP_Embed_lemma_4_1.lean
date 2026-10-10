-- Prove2me | Theorems.Thm_HomogLCP_Embed_lemma_4_1
-- name    : HomogLCP.Embed.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:44:09.571982+00:00
-- url     : https://prove2.me/theorems/fb0b69c5-d2fd-4a56-8880-7022dad8014e
-- title:
--   Lemma 4.1, p. 7 — the Andersen–Ye embedding operator F is monotone
-- statement:
--   Let $M\in\mathbb R^{d\times d}$ satisfy $M+M^\top\succeq 0$ and $q\in\mathbb R^d$. The operator
--   $$\mathcal F(z,\tau)=\begin{bmatrix} Mz+q\tau\\ -z^\top Mz/\tau-z^\top q\end{bmatrix},\qquad \tau>0,$$
--   of (4.1) is monotone on $\mathbb R^d\times\mathbb R_{++}$: $(\mathcal F(u)-\mathcal F(w))^\top(u-w)\ge 0$ for all $u,w\in\operatorname{dom}\mathcal F$.
--
--   It is the first ingredient of the monotonicity of $\mathcal Q=\mathcal F\cup\mathcal I$.
--
--   **Formalization Note** Monotonicity of $M$, the standing assumption of §§3–4, is the explicit hypothesis `(M + Mᵀ).PosSemidef`; the lemma's sentence does not repeat it.
-- source:
--   O'Donoghue, Operator splitting for a homogeneous embedding of the linear complementarity problem, arXiv:2004.02177v4, p. 7, Lemma 4.1

import Mathlib
import Definitions.Def_HomogLCP_Embed_MonotoneOp
import Definitions.Def_HomogLCP_Embed_Setting

namespace HomogLCP.Embed

open Matrix

/-- Lemma 4.1, p. 7: the operator `ℱ` is monotone. -/
theorem lemma_4_1 {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → ℝ)
    (hM : (M + Mᵀ).PosSemidef) :
    IsMonotoneOp (embF M q) := by sorry

end HomogLCP.Embed
