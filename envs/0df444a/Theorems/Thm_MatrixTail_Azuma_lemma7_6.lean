-- Prove2me | Theorems.Thm_MatrixTail_Azuma_lemma7_6
-- name    : MatrixTail.Azuma.lemma7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:24:58.812982+00:00
-- url     : https://prove2.me/theorems/4e9dd71e-f932-4da4-be9c-785b10aa3843
-- title:
--   Lemma 7.6 (Symmetrization) — E tr e^{H+X} ≤ E tr e^{H+2εX} for E X = 0
-- statement:
--   Let $H$ be a fixed self-adjoint $d\times d$ complex matrix and let $X$ be a random self-adjoint $d\times d$ matrix with integrable entries and $\mathbb E X = 0$. Let $\varepsilon$ be a Rademacher random variable on the same probability space, independent of $X$, such that $\mathbb E\operatorname{tr}e^{H+2\varepsilon X}$ is finite. Then
--   $$
--   \mathbb E \operatorname{tr} e^{H+X} \le \mathbb E\operatorname{tr} e^{H+2\varepsilon X}.
--   $$
--
--   Symmetrization injects an independent random sign into a centred random matrix at the cost of a factor $2$. In the matrix Azuma inequality this is what replaces the centring hypothesis by a symmetric variable whose conditional moment generating function can be bounded; the factor $2$ is the source of the constant $1/8$ in the final bound.
--
--   **Formalization Note** The trace exponential is the real part of the trace of the matrix exponential defined by the continuous functional calculus. The finiteness of the right-hand expectation is an explicit integrability hypothesis; without it the Lean integral would default to $0$.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 28, Lemma 7.6 (Symmetrization)

import Mathlib
import Definitions.Def_MatrixTail_Azuma_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Azuma

/-- **Lemma 7.6 (Symmetrization).** Tropp, *User-Friendly Tail Bounds for Sums of Random Matrices*,
arXiv:1004.4389v7, p. 28: "Let `H` be a fixed s.a. matrix, and let `X` be a random s.a. matrix with
`E X = 0`. Then `E tr e^{H+X} ≤ E tr e^{H+2εX}`, where `ε` is a Rademacher variable independent from `X`."

**Formalization Note.**
* Complex Hermitian `d × d` matrices; `tr e^·` is `trExp` (`cfc Real.exp`, real part of the trace); `E X` is
  the entrywise expectation (`mean`) and `E X = 0` is `mean P X = 0`.
* `X` is measurable, Hermitian at every outcome, with integrable entries (§2.2 regularity, needed for `E X`).
* `ε` lives on the same probability space as `X`, is Rademacher (`IsRademacher`) and `IndepFun ε X P`.
* Regularity (§2.2): `ω ↦ tr e^{H + 2ε(ω)X(ω)}` is integrable, so the right side is the paper's expectation
  and not Lean's junk value `0` (trap 2). The left side needs no hypothesis: its integrand is nonnegative and
  the inequality shows its expectation is finite whenever the right side is. -/
theorem lemma7_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) (X : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hX_meas : Measurable X) (hX_herm : ∀ ω, (X ω).IsHermitian) (hX_int : MatIntegrable P X)
    (hX_mean : mean P X = 0) (ε : Ω → ℝ) (hε : IsRademacher P ε) (hεX : IndepFun ε X P)
    (hint : Integrable (fun ω => trExp (H + (2 * ε ω) • X ω)) P) :
    ∫ ω, trExp (H + X ω) ∂P ≤ ∫ ω, trExp (H + (2 * ε ω) • X ω) ∂P := by sorry

end MatrixTail.Azuma
