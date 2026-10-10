-- Prove2me | Theorems.Thm_HomogLCP_Embed_lemma_4_4
-- name    : HomogLCP.Embed.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:43:23.094717+00:00
-- url     : https://prove2.me/theorems/84599bf3-7940-4b7f-9b47-373fd11f56fe
-- title:
--   Lemma 4.4, p. 10 — for monotone M the embedding operator Q = F ∪ I is maximal monotone
-- statement:
--   Let $M\in\mathbb R^{d\times d}$ be monotone, $M+M^\top\succeq 0$, and $q\in\mathbb R^d$. Let $\mathcal F$ be the Andersen–Ye operator (4.1) on $\mathbb R^d\times\mathbb R_{++}$ and $\mathcal I$ the infeasibility operator (4.7) with domain $\{(z,0)\mid z^\top Mz=0\}$. Then the operator
--   $$\mathcal Q=\mathcal F\cup\mathcal I$$
--   on $\mathbb R^{d+1}=\mathbb R^d\times\mathbb R$ is maximal monotone: it is monotone, and it is not strictly contained in any other monotone operator on $\mathbb R^d\times\mathbb R$.
--
--   Since the normal cone operator $N_{\mathcal C_+}$ is also maximal monotone, this makes the homogeneous embedding $0\in\mathcal Q(u)+N_{\mathcal C_+}(u)$ of $\mathrm{LCP}(M,q,\mathcal C)$ a sum of two maximal monotone operators, to which Douglas–Rachford splitting applies with guaranteed convergence (Algorithm 5.1).
--
--   **Formalization Note** "$M$ is monotone" is the standing assumption of §§3–4 and is the explicit hypothesis `(M + Mᵀ).PosSemidef`; without it Lemma 4.1 and the statement fail. The cone $\mathcal C$ does not enter $\mathcal Q$ and is not a hypothesis. Maximality is the containment form over all monotone operators (graphs) on `(Fin d → ℝ) × ℝ`. The case $d=0$ is allowed and the statement is true there.
-- source:
--   O'Donoghue, Operator splitting for a homogeneous embedding of the linear complementarity problem, arXiv:2004.02177v4, p. 10, Lemma 4.4 (proof pp. 11–12)

import Mathlib
import Definitions.Def_HomogLCP_Embed_MonotoneOp
import Definitions.Def_HomogLCP_Embed_Setting

namespace HomogLCP.Embed

open Matrix

/-- Lemma 4.4, p. 10: for monotone `M`, the operator `𝒬 = ℱ ∪ ℐ` is maximal monotone. -/
theorem lemma_4_4 {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → ℝ)
    (hM : (M + Mᵀ).PosSemidef) :
    IsMaximalMonotoneOp (embQ M q) := by sorry

end HomogLCP.Embed
