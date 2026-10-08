-- Prove2me | Theorems.Thm_MatrixTail_Gaussian_lemma4_3_rademacher
-- name    : MatrixTail.Gaussian.lemma4_3_rademacher
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:11:00.868237+00:00
-- url     : https://prove2.me/theorems/e0b02e24-5ddf-47a5-9b84-a6cbd76df9e4
-- title:
--   Lemma 4.3 (Rademacher half) — E e^{εθA} ≼ e^{θ²A²/2}
-- statement:
--   Let $A$ be a self-adjoint complex $d\times d$ matrix and let $\varepsilon$ be a Rademacher random variable, $\mathbb P\{\varepsilon=1\}=\mathbb P\{\varepsilon=-1\}=1/2$. Then for every $\theta\in\mathbb R$,
--   $$\mathbb E\, e^{\varepsilon\theta A}\preccurlyeq e^{\theta^2A^2/2}.$$
--
--   This is the semidefinite bound on the matrix mgf of a fixed matrix modulated by a random sign; it feeds Corollary 3.7 with $g(\theta)=\theta^2/2$ in the proof of the Rademacher series bound.
--
--   **Formalization Note** The expectation is entrywise; no integrability hypothesis is needed because $\varepsilon=\pm1$ almost surely.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 15, Lemma 4.3

import Mathlib
import Definitions.Def_MatrixTail_Gaussian_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Gaussian

/-- **Lemma 4.3** (Rademacher and Gaussian mgfs), Rademacher half, Tropp, arXiv:1004.4389v7, p. 15: if `A`
is a self-adjoint matrix and `ε` a Rademacher random variable, then `E e^{εθA} ≼ e^{θ²A²/2}` for `θ ∈ ℝ`.

Formalization Note. Complex Hermitian `d × d` matrices; `exp` is `cfc`; `E` is the entrywise expectation;
`≼` is the Loewner order under `MatrixOrder`. No integrability hypothesis: `ε` takes the values `±1` almost
surely, so `e^{εθA}` is bounded. `P` is a probability measure. -/
theorem lemma4_3_rademacher {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (ε : Ω → ℝ) (hε : IsRademacher P ε)
    (θ : ℝ) :
    MatrixTail.Master.mean P (fun ω => MatrixTail.Master.mexp ((ε ω * θ) • A)) ≤ MatrixTail.Master.mexp ((θ ^ 2 / 2) • A ^ 2) := by sorry

end MatrixTail.Gaussian
