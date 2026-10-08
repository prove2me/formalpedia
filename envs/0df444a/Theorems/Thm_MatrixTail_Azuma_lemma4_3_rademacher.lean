-- Prove2me | Theorems.Thm_MatrixTail_Azuma_lemma4_3_rademacher
-- name    : MatrixTail.Azuma.lemma4_3_rademacher
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:25:07.032095+00:00
-- url     : https://prove2.me/theorems/69286823-5dfa-464c-b7fc-59ea9086570b
-- title:
--   Lemma 4.3 (Rademacher half) — E e^{εθA} ≼ e^{θ²A²/2}
-- statement:
--   Let $A$ be a self-adjoint $d\times d$ complex matrix, let $\varepsilon$ be a Rademacher random variable ($\mathbb P\{\varepsilon=1\}=\mathbb P\{\varepsilon=-1\}=1/2$), and let $\theta\in\mathbb R$. Then, in the semidefinite order,
--   $$
--   \mathbb E\, e^{\varepsilon\theta A} \preceq e^{\theta^2A^2/2}.
--   $$
--
--   This is the semidefinite bound for the moment generating function of a fixed matrix modulated by a random sign. It is the Rademacher half of Lemma 4.3 of the paper; the Gaussian half, $\mathbb E e^{\gamma\theta A} = e^{\theta^2A^2/2}$ for a standard normal $\gamma$, is not stated here. In the matrix Azuma argument it is applied conditionally to bound the cumulant generating function of a symmetrized difference (Lemma 7.7).
--
--   **Formalization Note** The expectation is entrywise and $\preceq$ means that the difference is positive semidefinite. No integrability hypothesis is needed, since $\varepsilon=\pm1$ almost surely.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 15, Lemma 4.3 (Rademacher half)

import Mathlib
import Definitions.Def_MatrixTail_Azuma_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Azuma

/-- **Lemma 4.3** (Rademacher and Gaussian mgfs), Rademacher half, Tropp, arXiv:1004.4389v7, p. 15: if `A`
is a self-adjoint matrix and `ε` a Rademacher random variable, then `E e^{εθA} ≼ e^{θ²A²/2}` for `θ ∈ ℝ`.
The Gaussian half (`E e^{γθA} = e^{θ²A²/2}`) is not posed in this mission: only the Rademacher half is used,
in the proof of Lemma 7.7 (p. 29).

Formalization Note. Complex Hermitian `d × d` matrices; `exp` is `cfc`; `E` is the entrywise expectation;
`≼` is the Loewner order under `MatrixOrder`. No integrability hypothesis: `ε` takes the values `±1` almost
surely, so `e^{εθA}` is bounded. `P` is a probability measure. -/
theorem lemma4_3_rademacher {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) (ε : Ω → ℝ) (hε : IsRademacher P ε)
    (θ : ℝ) :
    mean P (fun ω => mexp ((ε ω * θ) • A)) ≤ mexp ((θ ^ 2 / 2) • A ^ 2) := by sorry

end MatrixTail.Azuma
