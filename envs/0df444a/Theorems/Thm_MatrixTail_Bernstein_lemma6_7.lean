-- Prove2me | Theorems.Thm_MatrixTail_Bernstein_lemma6_7
-- name    : MatrixTail.Bernstein.lemma6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:12:37.187983+00:00
-- url     : https://prove2.me/theorems/3e9fe2de-ad90-447b-8b49-a6cd6dcd53d2
-- title:
--   Lemma 6.7 — bounded Bernstein mgf: E X = 0, λmax(X) ≤ 1 ⟹ E e^{θX} ≼ exp((e^θ − θ − 1) · E X²)
-- statement:
--   Let $X$ be a random self-adjoint $d\times d$ complex matrix such that
--   $$\mathbb E X=0\qquad\text{and}\qquad\lambda_{\max}(X)\le 1\ \text{almost surely}.$$
--   Then for every $\theta>0$,
--   $$\mathbb E\,e^{\theta X}\preccurlyeq\exp\big((e^{\theta}-\theta-1)\cdot\mathbb E(X^2)\big).$$
--
--   This is the matrix analogue of the classical mgf bound for a centred random variable bounded above, and it feeds Corollary 3.7 with $g(\theta)=e^\theta-\theta-1$ and $A_k=\mathbb E(X_k^2)$ in the proof of the matrix Bennett inequality.
--
--   **Formalization Note** The entries of $X$ and $X^2$ are assumed integrable, so that $\mathbb E X$ and $\mathbb E(X^2)$ exist (the paper's standing regularity). The bound $\lambda_{\max}(X)\le1$ is assumed almost surely. Nothing is assumed about the smallest eigenvalue.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 25, Lemma 6.7

import Mathlib
import Definitions.Def_MatrixTail_Bernstein_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Bernstein

/-- **Lemma 6.7** (Bounded Bernstein mgf), Tropp, arXiv:1004.4389v7, p. 25.
If `X` is a random self-adjoint `d × d` complex matrix with `E X = 0` and `λmax(X) ≤ 1`, then
`E e^{θX} ≼ exp((e^θ − θ − 1) · E(X²))` for every `θ > 0`.

Formalization Note: `λmax(X) ≤ 1` is read almost surely (a property of a random matrix; it is the reading of
Theorem 6.1, which says "almost surely"). The entries of `X` and `X²` are integrable: the §2.2 regularity
that makes `E X` and `E(X²)` exist (without it `E(X²)` would be the junk value `0`). The mgf `E e^{θX}` needs
no hypothesis: `0 ≼ e^{θX} ≼ e^θ I` a.s. makes it integrable. Matrices are complex, `exp` is `cfc`, the
expectation is entrywise and `≼` is Mathlib's Loewner order. -/
theorem lemma6_7 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (X : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hX_meas : Measurable X) (hX_herm : ∀ ω, (X ω).IsHermitian)
    (hX_int : MatrixTail.Master.MatIntegrable P X) (hX2_int : MatrixTail.Master.MatIntegrable P (fun ω => X ω ^ 2))
    (hX_mean : MatrixTail.Master.mean P X = 0) (hX_max : ∀ᵐ ω ∂P, MatrixTail.Master.lambdaMax (X ω) ≤ 1)
    (θ : ℝ) (hθ : 0 < θ) :
    MatrixTail.Master.mean P (fun ω => MatrixTail.Master.mexp (θ • X ω)) ≤
      MatrixTail.Master.mexp ((Real.exp θ - θ - 1) • MatrixTail.Master.mean P (fun ω => X ω ^ 2)) := by sorry

end MatrixTail.Bernstein
