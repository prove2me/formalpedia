-- Prove2me | Theorems.Thm_MatrixTail_Gaussian_lemma4_3_gaussian
-- name    : MatrixTail.Gaussian.lemma4_3_gaussian
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:11:09.985851+00:00
-- url     : https://prove2.me/theorems/5c189cdb-4e8e-46ce-945d-2cfa0faf8008
-- title:
--   Lemma 4.3 (Gaussian half) — E e^{γθA} = e^{θ²A²/2}
-- statement:
--   Let $A$ be a self-adjoint complex $d\times d$ matrix and let $\gamma$ be a standard normal random variable. Then for every $\theta\in\mathbb R$,
--   $$\mathbb E\, e^{\gamma\theta A} = e^{\theta^2A^2/2}.$$
--
--   This is the exact matrix mgf of a fixed matrix modulated by a Gaussian; it is the matrix analogue of $\mathbb E e^{\theta\gamma a}=e^{\theta^2a^2/2}$ and feeds Corollary 3.7 with $g(\theta)=\theta^2/2$ in the proof of the Gaussian series bound.
--
--   **Formalization Note** The expectation is entrywise. No integrability hypothesis is added: each entry of $e^{\gamma\theta A}$ is bounded by $e^{|\gamma\theta|\,\|A\|}$, which is integrable.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 15, Lemma 4.3

import Mathlib
import Definitions.Def_MatrixTail_Gaussian_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Gaussian

/-- **Lemma 4.3** (Rademacher and Gaussian mgfs), Gaussian half, Tropp, arXiv:1004.4389v7, p. 15: if `A` is
a self-adjoint matrix and `γ` a standard normal random variable, then `E e^{γθA} = e^{θ²A²/2}` for
`θ ∈ ℝ` (an equality, not only `≼`).

Formalization Note. Complex Hermitian `d × d` matrices; `exp` is `cfc`; `E` is the entrywise expectation.
No integrability hypothesis is added: every entry of `e^{γθA}` is bounded by `e^{|γθ|‖A‖}`, which is
integrable because the Gaussian mgf is finite, so the expectation is a genuine one. `P` is a probability
measure. -/
theorem lemma4_3_gaussian {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (γ : Ω → ℝ) (hγ : IsStdGaussian P γ)
    (θ : ℝ) :
    MatrixTail.Master.mean P (fun ω => MatrixTail.Master.mexp ((γ ω * θ) • A)) = MatrixTail.Master.mexp ((θ ^ 2 / 2) • A ^ 2) := by sorry

end MatrixTail.Gaussian
