-- Prove2me | Theorems.Thm_IterRoundDet_lemma_4_2
-- name    : IterRoundDet.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:30.787296+00:00
-- url     : https://prove2.me/theorems/3363af08-97b0-49b7-9791-69874f4c211b
-- title:
--   Lemma 4.2 — Hölder continuity of $E_p$, $f$, $f-g_1$, $f-g_2$, $\Psi$ with $K=\mathrm{poly}(n,b)$
-- statement:
--   There is a $K=\mathrm{poly}(n,b)$ such that for all points $(a,x),(a',x')\in\mathcal R$,
--
--   $$|E_p(a)-E_p(a')|\le K\sqrt{\|a-a'\|_1}\quad\text{and}\quad|G(a,x)-G(a',x')|\le K\sqrt{\|a-a'\|_1+\|x-x'\|_1},$$
--
--   where $G$ ranges over $\{f,f-g_1,f-g_2,\Psi\}$. It bounds the loss of every discretization step of the algorithm.
--
--   **Formalization Note** $K=C(2+n+b)^{K_0}$, with $C,K_0$ chosen before the instance. The proof rests on a bounded-dual theorem of Straszak and Vishnoi, which is not a hypothesis here.
--
--   Differences from the source:
--   - encoding: a homogeneous multiaffine polynomial p of degree d → its coefficient function c with c S ≠ 0 → |S| = d; reason: footnote 2 is this form; the two are in bijection
--   - encoding: all coefficients have the same sign → non-negative coefficients inside IsStablePoly; reason: footnote 2 and §3.1 normalize to this; for a negative p the printed logarithms have no meaning
--   - encoding: K = poly(n, b) → K = C(2 + n + b)^{K₀} with C, K₀ before n; reason: the standard unfolding of poly
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 4.2, (30), p.20; proof pp.36–37

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Polytopes
import Definitions.Def_IterRoundDet_Relaxation
import Definitions.Def_IterRoundDet_Regularizer
import Definitions.Def_IterRoundDet_Oracles

set_option autoImplicit false

namespace IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 4.2 (Continuity), p.20. There is a `K = poly(n, b)` such that for all points
`(a, x), (a′, x′) ∈ R`, `|E_p(a) − E_p(a′)| ≤ K √‖a − a′‖₁` and `|G(a, x) − G(a′, x′)| ≤ K √(‖a − a′‖₁ + ‖x − x′‖₁)`, (30),
where `G` ranges over `{f, f − g₁, f − g₂, Ψ}`.

**Formalization Note.** `K := C (2 + n + b)^{K₀}` with `C, K₀` chosen before the instance; `2 +` keeps the base above `1`. -/
theorem lemma_4_2 :
    ∃ C K₀ : ℕ, ∀ (n d b : ℕ) (c : Finset (Fin n) → ℚ) (M : Matroid (Fin n)),
      IsStablePoly d (castCoef c) → M.E = Set.univ → BitBounded b c →
      ∀ a x a' x' : Fin n → ℝ, Feasible (castCoef c) M a x → Feasible (castCoef c) M a' x' →
        let K : ℝ := ((C * (2 + n + b) ^ K₀ : ℕ) : ℝ)
        let δa : ℝ := ∑ i, |a i - a' i|
        let δ : ℝ := δa + ∑ i, |x i - x' i|
        |Ep (castCoef c) a - Ep (castCoef c) a'| ≤ K * Real.sqrt δa ∧
        |relaxObj (castCoef c) a x - relaxObj (castCoef c) a' x'| ≤ K * Real.sqrt δ ∧
        |fMinusG1 (castCoef c) d a x - fMinusG1 (castCoef c) d a' x'| ≤ K * Real.sqrt δ ∧
        |fMinusG2 (castCoef c) a x - fMinusG2 (castCoef c) a' x'| ≤ K * Real.sqrt δ ∧
        |Psi (castCoef c) d a x - Psi (castCoef c) d a' x'| ≤ K * Real.sqrt δ := by sorry

end IterRoundDet
