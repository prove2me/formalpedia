-- Prove2me | Theorems.Thm_LinfContractionFP_eq_4
-- name    : LinfContractionFP.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:17:52.333274+00:00
-- url     : https://prove2.me/theorems/b0217bc4-4acb-4a69-bfda-1c82d8905927
-- title:
--   Eq. (4) — $\sigma_{\min}\le t-\|x-x^*\|$ and $\sigma_{\max}\ge t+\|x-x^*\|$
-- statement:
--   Let $0<\gamma\le1$, $f$ a $(1-\gamma)$-contraction of $[0,1]^d$ with fixed point $x^*$, $[L,U]$ a possibly degenerate box and $\eta>0$. Let $x$ be the candidate point of ThinLabel (Algorithm 2, line 8), computed with recursive solves that return $\gamma\eta/2$-near fixed points, and let $t$ be the median of the half side lengths $(U_i-L_i)/2$. If $\|x-f(x)\|_\infty>\eta$, then the smallest and largest face slacks satisfy
--   $$\sigma_{\min}\le t-\|x-x^*\|_\infty\qquad\text{and}\qquad\sigma_{\max}\ge t+\|x-x^*\|_\infty .$$
--   This separation is the crux of Lemma 2.
--
--   Differences from the source:
--   - generalization: the recursive calls of Solve inside ThinLabel → any procedure solveSub meeting SubSolverSpec (η'-near fixed points of (1−γ)-contractions of dimension ≤ d/2); reason: this is the paper's inductive hypothesis; Solve itself meets it, so the statement specializes to the paper's
--   - reading: median → lower median; reason: the proof uses only that the narrow and wide sets have at most d/2 elements
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), proof of Lemma 2, display (4), p.8 (cases 1–3, pp.9–11)

import Mathlib
import Definitions.Def_LinfContractionFP_IsContraction
import Definitions.Def_LinfContractionFP_SubSolverSpec
import Definitions.Def_LinfContractionFP_thinPoint
import Definitions.Def_LinfContractionFP_slack

namespace LinfContractionFP

/-- Display (4), in the proof of Lemma 2: if the candidate point `x` of ThinLabel (line 8) has
`‖x − f(x)‖∞ > η`, then the minimum and maximum face slacks are separated from the median half
side `t`: `σmin ≤ t − ‖x − x*‖∞` and `σmax ≥ t + ‖x − x*‖∞`.

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), proof of Lemma 2, p.8: "So, consider the case ‖x − f(x)‖∞ > η, which implies
‖x − x*‖∞ > η/2 by Lemma 1. The crux of the proof is to show that when that is the case, σmin
and σmax are sufficiently separated from the median half-side t, specifically
σmin ≤ t − ‖x − x*‖∞ and σmax ≥ t + ‖x − x*‖∞. (4)"

**Formalization Note.** `x = thinPoint …` (Algorithm 2, lines 1–8), `f` is the clipped
extension, `t` the lower median of the half side lengths `(U_i − L_i)/2`, `σmin`, `σmax` the
minimum and maximum of the `2d` face slacks (`⨅`, `⨆` over `ι × Bool`). The recursive solves
are any `solveSub` meeting `SubSolverSpec` (the paper's inductive hypothesis). The box may be
degenerate. -/
theorem eq_4 {ι : Type} [Fintype ι] (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (f : (ι → ℝ) → (ι → ℝ)) (hf : IsContraction γ f) (xs : ι → ℝ) (hxs : xs ∈ unitCube ι)
    (hfix : f xs = xs) (solveSub : (S : Finset ι) → ((↥S → ℝ) → (↥S → ℝ)) → ℝ → (↥S → ℝ))
    (hsub : SubSolverSpec γ solveSub) (L U : ι → ℝ) (η : ℝ) (hη : 0 < η)
    (hfar : η < ‖thinPoint γ f solveSub L U η - clipExt f (thinPoint γ f solveSub L U η)‖) :
    (⨅ j, slack L U xs j) ≤
        lowerMedian (fun i => (U i - L i) / 2) - ‖thinPoint γ f solveSub L U η - xs‖ ∧
      lowerMedian (fun i => (U i - L i) / 2) + ‖thinPoint γ f solveSub L U η - xs‖ ≤
        ⨆ j, slack L U xs j := by sorry

end LinfContractionFP
