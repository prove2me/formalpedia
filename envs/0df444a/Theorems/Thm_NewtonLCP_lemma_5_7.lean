-- Prove2me | Theorems.Thm_NewtonLCP_lemma_5_7
-- name    : NewtonLCP.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:28:52.400059+00:00
-- url     : https://prove2.me/theorems/eca0da1d-fced-4e88-bc6e-545eac58364f
-- title:
--   Lemma 5.7 — stability of Rump weights
-- statement:
--   For $A\in\mathcal P_\star\cap\mathbb R^{n\times n}$, $u\in\mathbb R^n_{>0}$ and $U=\mathrm{diag}(u)$, let $H=(I_n+A)^{-1}$ and $H'=(I_n+UAU)^{-1}$. Then, with $K=8$,
--
--   $$\|\log q_{H'}-\log q_H\|_\infty\le16K\,\|\log u\|_1 ,\qquad(13)$$
--
--   where logarithms are taken entrywise. A Newton step rescales the Newton matrix by such a $U$, so the weights change by a bounded factor between iterations.
--
--   Differences from the source: none.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Lemma 5.7, (13), p.15 (restated p.19, proof pp.19–21)

import Mathlib
import Definitions.Def_NewtonLCP_Handicap
import Definitions.Def_NewtonLCP_RumpWeight

open Matrix

namespace NewtonLCP

/-- **Lemma 5.7** (stability of Rump weights). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Lemma 5.7, (13), p.15 (restated p.19, proof
pp.19–21).

For `A ∈ P⋆ ∩ ℝⁿˣⁿ`, `u ∈ ℝⁿ_{>0}` and `U = diag(u)`, let `H = (Iₙ + A)⁻¹` and
`H' = (Iₙ + UAU)⁻¹`. Then `‖log q_{H'} − log q_H‖_∞ ≤ 16K‖log(u)‖₁` (13).

**Formalization Note.** `K = 8`, natural logarithm entrywise; the ∞-norm is stated for every
coordinate `j` and `‖log u‖₁ = Σᵢ |log uᵢ|`. -/
theorem lemma_5_7 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (u : ι → ℝ)
    (hA : IsPStar A) (hu : ∀ i, 0 < u i) (j : ι) :
    |Real.log (rumpWeight (1 + diagonal u * A * diagonal u)⁻¹ j) -
        Real.log (rumpWeight (1 + A)⁻¹ j)| ≤
      16 * 8 * ∑ i, |Real.log (u i)| := by sorry

end NewtonLCP
