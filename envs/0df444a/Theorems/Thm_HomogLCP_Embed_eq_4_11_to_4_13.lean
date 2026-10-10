-- Prove2me | Theorems.Thm_HomogLCP_Embed_eq_4_11_to_4_13
-- name    : HomogLCP.Embed.eq_4_11_to_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:43:10.983129+00:00
-- url     : https://prove2.me/theorems/5be6e58a-d61d-4f20-9bbb-442019190ec8
-- title:
--   (4.11)–(4.13), pp. 11–12 — an extension pair (p, r) of F with p_τ = 0 lies in I
-- statement:
--   Let $M\in\mathbb R^{d\times d}$ satisfy $M+M^\top\succeq 0$, $q\in\mathbb R^d$, and let $\mathcal F$ be the operator (4.1). Let $p=(p_z,0)$ and $r=(r_z,r_\tau)$ in $\mathbb R^d\times\mathbb R$, and suppose
--   $$0\le(\mathcal F(u)-r)^\top(u-p)\qquad\text{for all } u\in\operatorname{dom}\mathcal F .$$
--   Then
--   $$p_z^\top Mp_z=0\quad(4.11),\qquad Mp_z=r_z\quad(4.12),\qquad r_\tau\le -p_z^\top q\quad(4.13).$$
--
--   These three conditions are exactly $(p,r)\in\mathcal I$ by the definition (4.7); this is the case $p_\tau=0$ of the maximality argument for $\mathcal Q$.
--
--   **Formalization Note** The conclusion is the conjunction of the three displays, not membership in $\mathcal I$, so each display is visible; together with $p_\tau=0$ they unfold to membership. The page's "since $\tau\ge 0$" before (4.13) refers to $\tau>0$ on $\operatorname{dom}\mathcal F$; nothing in the statement depends on it.
-- source:
--   O'Donoghue, Operator splitting for a homogeneous embedding of the linear complementarity problem, arXiv:2004.02177v4, pp. 11–12, proof of Lemma 4.4, (4.11), (4.12), (4.13)

import Mathlib
import Definitions.Def_HomogLCP_Embed_MonotoneOp
import Definitions.Def_HomogLCP_Embed_Setting

namespace HomogLCP.Embed

open Matrix

/-- (4.11)–(4.13), proof of Lemma 4.4, pp. 11–12: an extension pair `(p, r)` of `ℱ` with
`p = (p_z, 0)` satisfies `p_zᵀMp_z = 0`, `Mp_z = r_z` and `r_τ ≤ -p_zᵀq`, i.e. `(p, r) ∈ ℐ`. -/
theorem eq_4_11_to_4_13 {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → ℝ)
    (hM : (M + Mᵀ).PosSemidef) :
    ∀ p r : (Fin d → ℝ) × ℝ, p.2 = 0 →
      (∀ a ∈ embF M q, 0 ≤ pair (a.2 - r) (a.1 - p)) →
        p.1 ⬝ᵥ (M *ᵥ p.1) = 0 ∧ M *ᵥ p.1 = r.1 ∧ r.2 ≤ -(p.1 ⬝ᵥ q) := by sorry

end HomogLCP.Embed
