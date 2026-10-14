-- Prove2me | Theorems.Thm_MultivarScores_L2Rule_S_eq_S_prime_add
-- name    : MultivarScores.L2Rule.S_eq_S_prime_add
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:30:32.981229+00:00
-- url     : https://prove2.me/theorems/877db1ad-8c63-496a-be0b-f19089f30ef5
-- title:
--   §3.1, p. 8 — S(P, y) = S′(P, y) + ∫ w²(z − y) h(z) dz: the scores (2) and (3) differ by a term depending on y only
-- statement:
--   Let $P$ be a distribution on $\mathbb R^d$, $w$ a kernel, $h$ a weight and $y\in\mathbb R^d$. Suppose $(f_P*w)^2h$, $w(\cdot-y)^2h$ and $(f_P*w)(\cdot)\,w(\cdot-y)\,h$ are Lebesgue integrable. Then the L² scoring rules (2) and (3) satisfy
--
--   $$S(P,y;w,h)=S'(P,y;w,h)+\int_{\mathbb R^d}w^2(z-y)\,h(z)\,dz.$$
--
--   The last term depends on $y$ only, not on $P$; this is the sense in which the paper calls (3) "equivalent" to (2): both rules have the same divergence.
--
--   **Formalization Note** The three integrability hypotheses make each of the three integrals finite; without them a Bochner integral is $0$ and the identity can fail. They are the pointwise forms of Assumption 1(b)/(c).
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, p. 8, §3.1, the sentence between (2) and (3)

import Mathlib
import Definitions.Def_MultivarScores_L2Rule_Setting

namespace MultivarScores.L2Rule

open MeasureTheory

/-- (2)–(3) relation, §3.1, p. 8: `S(P, y) = S′(P, y) + ∫ w²(z − y) h(z) dz`, where the last term
depends on `y` only. -/
theorem S_eq_S_prime_add {d : ℕ} (P : Measure (E d)) (w h : E d → ℝ) (y : E d)
    (h_sq_smooth : Integrable (fun z => smooth P w z ^ 2 * h z))
    (h_sq_w : Integrable (fun z => w (z - y) ^ 2 * h z))
    (h_cross : Integrable (fun z => smooth P w z * w (z - y) * h z)) :
    S P w h y = S' P w h y + ∫ z, w (z - y) ^ 2 * h z := by sorry

end MultivarScores.L2Rule
