-- Prove2me | Theorems.Thm_KnownFidelity_Rank_lemma_3_1
-- name    : KnownFidelity.Rank.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:47:46.91288+00:00
-- url     : https://prove2.me/theorems/1c7d5234-d518-43d3-8ee6-1f23546935a9
-- title:
--   Lemma 3.1 — rescaled covariant measurement: $\mathbb E|\widehat F-\|\sqrt\sigma A\|_1|^2\le 4s\min\{s,h_\sigma\}/(n+1)$
-- statement:
--   Let $\sigma$ be a known state on $\mathbb C^d$, let $s\ge1$ and $n\ge1$. There is a single collective measurement on $n$ copies of a pure state in $\mathbb C^d\otimes\mathbb C^s$, with a real-valued outcome $\widehat F$, such that for **every** $A\in\mathbb C^{d\times s}$ with $\|A\|_F=1$, when it is applied to $n$ copies of $|\psi\rangle=\mathrm{vec}(A)$,
--
--   $$\mathbb E\,\Big|\widehat F-\big\|\sqrt\sigma A\big\|_1\Big|^2\ \le\ \frac{4s\min\{s,h_\sigma\}}{n+1},\qquad h_\sigma=(\mathrm{tr}\sqrt\sigma)^2 .$$
--
--   The bound does not depend on the ambient dimension $d$. Combined with the random-purification channel (Eq. (16)) it gives the estimator of Theorem 1.1, since $\|\sqrt\sigma A\|_1=F(\rho,\sigma)$ for every purification $\mathrm{vec}(A)$ of $\rho$.
--
--   **Formalization Note** The measurement is a POVM on `Fin n → Fin d × Fin s` with real outcomes, chosen before $A$; $\|\cdot\|_1$ is the rectangular trace norm and the risk is a lower integral.
--
--   Differences from the source:
--   - reading: there is an estimator (for every input of the stated class) → ∃ POVM with real outcomes, chosen before the input, ∀ input; reason: an estimator is a collective measurement plus classical post-processing, which a real-outcome POVM includes; the estimator does not know the unknown input (∀∃ would make the statement trivial)
--   - encoding: E|F̂ − ·|² (expectation) → lower Lebesgue integral of (x − v)² in [0, ∞] (mse); reason: a Bochner integral of a non-integrable square is 0 in Lean; the lower integral is the same expectation and never a junk value
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Lemma 3.1, p. 5 (PDF p. 7)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_mse
import Definitions.Def_KnownFidelity_Rank_vecProj
import Definitions.Def_KnownFidelity_Rank_hSigma
import Definitions.Def_WildeQIT_traceNorm

open MeasureTheory
open scoped Matrix ComplexOrder

namespace KnownFidelity.Rank

/-- **Lemma 3.1 (Rescaled covariant measurement).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Lemma 3.1, printed p. 5 (PDF p. 7): "Let A ∈ C^{d×s} satisfy ∥A∥_F = 1, and let
|ψ⟩ = vec(A). For a known state σ on C^d, there is an estimator from n ≥ 1 copies of |ψ⟩ such that
E|F̂ − ∥√σA∥₁|² ≤ 4s min{s, h_σ}/(n + 1)."

For every state `σ` on `ℂ^d`, every `s` and every `n ≥ 1` there is one POVM on
`(ℂ^d ⊗ ℂ^s)^{⊗n}` with real outcomes such that for **every** `A ∈ ℂ^{d×s}` with `‖A‖_F = 1`,
measured on `n` copies of `|vec A⟩⟨vec A|`, the mean-square error of the outcome around
`‖√σ A‖₁` is at most `4 s min{s, h_σ}/(n + 1)`.

**Formalization Note.** The estimator is chosen before `A` (it may depend on `σ, d, s, n` only);
the opposite order would make the lemma trivial. `‖·‖₁` is `WildeQIT.traceNorm` (rectangular),
`√σ = cfc Real.sqrt σ`, `h_σ = hSigma σ`, `vec` is Eq. (7) (system index first), and the
mean-square error is the lower integral `mse`. -/
theorem lemma_3_1 {d s : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : QAlgorithms.IsDensityMatrix σ)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ E : QAlgorithms.Measurements.OperatorPOVM (Fin n → Fin d × Fin s) ℝ,
      ∀ (A : Matrix (Fin d) (Fin s) ℂ) (hA : ∑ i, ∑ j, ‖A i j‖ ^ 2 = 1),
        mse n E (vecProj A) (isDensityMatrix_vecProj hA)
            (WildeQIT.traceNorm (cfc Real.sqrt σ * A)) ≤
          ENNReal.ofReal (4 * s * min (s : ℝ) (hSigma σ) / (n + 1)) := by sorry

end KnownFidelity.Rank
