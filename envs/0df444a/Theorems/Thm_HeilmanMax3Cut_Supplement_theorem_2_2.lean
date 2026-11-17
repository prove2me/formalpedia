-- Prove2me | Theorems.Thm_HeilmanMax3Cut_Supplement_theorem_2_2
-- name    : HeilmanMax3Cut.Supplement.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:10:17.972743+00:00
-- url     : https://prove2.me/theorems/be5ab99f-ffbb-431d-864e-8ae62af8527b
-- title:
--   Theorem 2.2 — positive vector-valued Borell inequality $\mathrm{Stab}_\eta(f)\le F^*(k,\eta)$ for mean-zero $f$
-- statement:
--   Let $n\ge k\ge3$ and let $f:\mathbb R^n\to B_k$ be measurable with
--
--   $$\int_{\mathbb R^n}f\,d\gamma_n=0 .$$
--
--   Let $0<\eta\le0.5843$ (or $0<\eta\le3/5$ if $k>3$). Then
--
--   $$\mathrm{Stab}_\eta(f)\ \le\ F^*(k,\eta).$$
--
--   So among mean-zero ball-valued functions, $f_{\mathrm{opt},k}$ maximizes noise stability at these positive correlations.
--
--   **Formalization Note** The mean-zero condition is the Bochner integral of $f$ in $\mathbb R^k$; $f$ is bounded and measurable, so it is integrable. $0.5843$ is the exact decimal $5843/10000$.
--
--   Differences from the source: none.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Theorem 2.2, p.9, Eq. (5)

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HeilmanMax3Cut_Supplement_stabVec
import Definitions.Def_HeilmanMax3Cut_Supplement_Fstar
open MeasureTheory OAI.GaussianPropeller

namespace HeilmanMax3Cut.Supplement

/-- **Theorem 2.2 (Positive vector-valued Borell inequality).** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Theorem 2.2, p.9: "Let
`n ≥ k ≥ 3`, let `f : ℝⁿ → B_k` be measurable with `∫_{ℝⁿ} f dγₙ = 0`. Let `0 < η ≤ 0.5843` (or
`0 < η ≤ 3/5` if `k > 3`). Then `Stab_η(f) ≤ F*(k, η)`. (5)"

**Formalization Note.** `f : Space n → EuclideanSpace ℝ (Fin k)` is measurable with `‖f x‖ ≤ 1` for
every `x`; the mean-zero condition is the Bochner integral `∫ f dγₙ = 0` in `ℝᵏ` (`f` is bounded and
measurable, hence integrable, so the condition is not vacuous). The range is `0 < η` together with
`η ≤ 0.5843 = 5843/10000`, or, when `k > 3`, `η ≤ 3/5`. -/
theorem theorem_2_2 (n k : ℕ) (hk : 3 ≤ k) (hkn : k ≤ n)
    (f : Space n → EuclideanSpace ℝ (Fin k)) (hf : Measurable f) (hB : ∀ x, ‖f x‖ ≤ 1)
    (hmean : ∫ x, f x ∂(gaussian n) = 0)
    (η : ℝ) (hη : 0 < η) (hη' : η ≤ (5843 / 10000 : ℝ) ∨ (3 < k ∧ η ≤ (3 / 5 : ℝ))) :
    stabVec n k η f ≤ Fstar k η := by sorry

end HeilmanMax3Cut.Supplement
