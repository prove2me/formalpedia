-- Prove2me | Theorems.Thm_IterRoundDet_lemma_3_7
-- name    : IterRoundDet.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:19.248808+00:00
-- url     : https://prove2.me/theorems/079b5b0f-c3a0-435c-ba14-89c9eaa40701
-- title:
--   Lemma 3.7 — $H_+\ge 0$, $0\le H_-\le d$, $2H_+-9H_-\le m/6$; $g_1<g_2$ forces $m>12d$
-- statement:
--   For $(a,x)\in\mathcal R$ where $x$ has at most $m$ fractional coordinates,
--
--   $$H_+(a,x)\ge 0,\qquad 0\le H_-(a,x)\le d,\qquad 2H_+(a,x)-9H_-(a,x)\le m/6.$$
--
--   In particular $g_1(a,x)<g_2(a,x)$ implies $m>12d$. These bounds give $0\le g\le 14d$ and select the branch of $\Psi$ used in the second-order step.
--
--   Differences from the source:
--   - encoding: a homogeneous multiaffine polynomial p of degree d → its coefficient function c with c S ≠ 0 → |S| = d; reason: footnote 2 is this form; the two are in bijection
--   - encoding: all coefficients have the same sign → non-negative coefficients inside IsStablePoly; reason: footnote 2 and §3.1 normalize to this; for a negative p the printed logarithms have no meaning
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.7, p.16; proof pp.35–36

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Polytopes
import Definitions.Def_IterRoundDet_Relaxation
import Definitions.Def_IterRoundDet_Regularizer

set_option autoImplicit false

namespace IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.7, p.16. For `(a, x) ∈ R` where `x` has at most `m` fractional coordinates,
`H₊(a, x) ≥ 0`, `0 ≤ H₋(a, x) ≤ d`, `2H₊(a, x) − 9H₋(a, x) ≤ m/6`. In particular `g₁(a, x) < g₂(a, x)` implies `m > 12d`. -/
theorem lemma_3_7 {n d m : ℕ} {c : Finset (Fin n) → ℝ} (hc : IsStablePoly d c)
    {M : Matroid (Fin n)} (hM : M.E = Set.univ) {a x : Fin n → ℝ} (hax : Feasible c M a x)
    (hm : (fractional x).card ≤ m) :
    0 ≤ Hplus a x ∧ 0 ≤ Hminus a x ∧ Hminus a x ≤ d ∧
    2 * Hplus a x - 9 * Hminus a x ≤ (m : ℝ) / 6 ∧
    (g1 d a x < g2 a x → 12 * (d : ℝ) < m) := by sorry

end IterRoundDet
