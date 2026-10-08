-- Prove2me | Theorems.Thm_GloriaOtto_Variance_lemma_2_6
-- name    : GloriaOtto.Variance.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:17.455168+00:00
-- url     : https://prove2.me/theorems/eef5a2bf-da41-429e-92b5-aa3b59b873c3
-- title:
--   Lemma 2.6 — G_T(x, y; ·) and φ_T(x; ·) are continuous on A_αβ for the product topology, hence Borel measurable
-- statement:
--   Let $d \ge 2$, $0 < \alpha \le \beta$, $T > 0$, $\xi \in \mathbb R^d$ and $x, y \in \mathbb Z^d$. Equip $\mathbb R^E$, $E$ the set of edges, with the product topology. Then
--   1. $a \mapsto G_T(x,y;a)$ and $a \mapsto \phi_T(x;a)$ are continuous on $\mathcal A_{\alpha\beta}$;
--   2. in particular, both maps are Borel measurable functions of $a \in \mathcal A_{\alpha\beta}$.
--
--   This is the measurability needed to apply Lemma 2.3 to $\phi_T(x;\cdot)$ and nonlinear functions of it.
--
--   **Formalization Note.** Continuity is `ContinuousOn` on the set $\mathcal A_{\alpha\beta}$; measurability is for the subtype $\{a : a \in \mathcal A_{\alpha\beta}\}$ with the σ-algebra induced by the product σ-algebra.
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, Lemma 2.6, p. 17

import Mathlib
import Definitions.Def_GloriaOtto_Variance_Setup

open MeasureTheory ProbabilityTheory

namespace GloriaOtto.Variance

theorem lemma_2_6 (d : ℕ) (hd : 2 ≤ d) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β)
    (T : ℝ) (hT : 0 < T) (ξ : Fin d → ℝ) (x y : Site d) :
    ContinuousOn (fun a : Edge d → ℝ => greenT a T x y) {a | InA α β a} ∧
    ContinuousOn (fun a : Edge d → ℝ => phiT a T ξ x) {a | InA α β a} ∧
    Measurable (fun a : {a : Edge d → ℝ // InA α β a} => greenT a.1 T x y) ∧
    Measurable (fun a : {a : Edge d → ℝ // InA α β a} => phiT a.1 T ξ x) := by sorry

end GloriaOtto.Variance
