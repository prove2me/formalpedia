-- Prove2me | Theorems.Thm_HomogLCP_Embed_no_extension_in_domF
-- name    : HomogLCP.Embed.no_extension_in_domF
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:43:24.785977+00:00
-- url     : https://prove2.me/theorems/241aaf98-e148-41d4-99bb-832e505afcfb
-- title:
--   Proof of Lemma 4.4, p. 11 — no monotone extension pair (p, r) of F with p ∈ dom(F)
-- statement:
--   Let $M\in\mathbb R^{d\times d}$ satisfy $M+M^\top\succeq 0$, $q\in\mathbb R^d$, and let $\mathcal F$ be the operator (4.1) on $\mathbb R^d\times\mathbb R_{++}$. Let $p=(p_z,p_\tau)$ with $p_\tau>0$ and $r\in\mathbb R^d\times\mathbb R$, and suppose $\mathcal F\cup\{(p,r)\}$ is monotone, i.e.
--   $$(\mathcal F(u)-r)^\top(u-p)\ \ge\ 0\qquad\text{for all } u\in\operatorname{dom}\mathcal F .$$
--   Then $(p,r)\in\mathcal F$, i.e. $r=\mathcal F(p)$: there is no genuine extension pair of $\mathcal F$ with $p\in\operatorname{dom}\mathcal F$.
--
--   This is the case $p_\tau>0$ of the maximality argument for $\mathcal Q$.
--
--   **Formalization Note** "$\mathcal F\cup\{(p,r)\}$ is monotone" is written as the inequality against every pair of $\mathcal F$; pairs inside $\mathcal F$ are monotone by Lemma 4.1. "No such extension pair exists" is stated as "the pair already belongs to $\mathcal F$". The standing assumption $M+M^\top\succeq 0$ is kept as a hypothesis.
-- source:
--   O'Donoghue, Operator splitting for a homogeneous embedding of the linear complementarity problem, arXiv:2004.02177v4, p. 11, proof of Lemma 4.4 ("no such extension pair with p ∈ dom(F) exists")

import Mathlib
import Definitions.Def_HomogLCP_Embed_MonotoneOp
import Definitions.Def_HomogLCP_Embed_Setting

namespace HomogLCP.Embed

open Matrix

/-- Proof of Lemma 4.4, p. 11: no extension pair `(p, r)` of `ℱ` has `p ∈ dom ℱ`. If
`p_τ > 0` and `(p, r)` is monotonically related to every pair of `ℱ`, then `(p, r) ∈ ℱ`,
i.e. `r = ℱ(p)`. -/
theorem no_extension_in_domF {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → ℝ)
    (hM : (M + Mᵀ).PosSemidef) :
    ∀ p r : (Fin d → ℝ) × ℝ, 0 < p.2 →
      (∀ a ∈ embF M q, 0 ≤ pair (a.2 - r) (a.1 - p)) → (p, r) ∈ embF M q := by sorry

end HomogLCP.Embed
