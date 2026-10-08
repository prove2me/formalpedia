-- Prove2me | Theorems.Thm_HighDimStat_RandomMatrices_thresholded_covariance_estimation_bound_v2
-- name    : HighDimStat.RandomMatrices.thresholded_covariance_estimation_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:20:32.844988+00:00
-- url     : https://prove2.me/theorems/fc689528-bde4-44f1-b7ec-403f226fe1c8
-- title:
--   Theorem 6.23 — thresholding-based covariance estimation ($d\ge1$, $\Sigma\ne0$)
-- statement:
--   **Theorem 6.23 (Thresholding-based covariance estimation).** Let $\{x_i\}_{i=1}^n$ be an
--   i.i.d. sequence of zero-mean random vectors in $\mathbb R^d$, $d\ge1$, with a nonzero
--   covariance matrix $\Sigma$, and suppose that each component $x_{ij}$ is sub-Gaussian with
--   parameter at most $\sigma$. If $n>\log d$, then for any $\delta>0$, the thresholded sample
--   covariance matrix $T_{\lambda_n}(\hat\Sigma)$ with $\lambda_n/\sigma^2 = 8\sqrt{\log d/n}+\delta$
--   satisfies
--
--   $$
--   \mathbb P\big[\,|\!|\!|T_{\lambda_n}(\hat\Sigma)-\Sigma|\!|\!|_2 \ge 2|\!|\!|A|\!|\!|_2\lambda_n\,\big]
--   \;\le\; 8e^{-\frac{n}{16}\min\{\delta,\delta^2\}},
--   $$
--
--   where $A$ is the adjacency matrix of the sparsity graph of $\Sigma$ ($A_{j\ell}=\mathbb 1[\Sigma_{j\ell}\ne0]$).
--
--   This is the chapter's title result for structured (sparse) covariance estimation: when the
--   zero pattern of $\Sigma$ is unknown but its adjacency-graph sparsity $|\!|\!|A|\!|\!|_2$ is
--   controlled, simple entrywise thresholding of the sample covariance matrix attains an error
--   that scales with the graph's sparsity rather than the ambient dimension $d$.
--
--   **Formalization Note.** The retired version (`thresholded_covariance_estimation_bound`)
--   admitted $d=0$: Lean's $\log 0=0$ makes $n>\log d$ vacuous, every coordinatewise hypothesis is
--   vacuous over $\mathrm{Fin}\,0$, both operator norms on $\mathbb R^0$ are $0$, so the event
--   $0\le0$ is certain while the right side is $<1$ (accepted disproof). The new statement adds
--   `hd : 1 ≤ d` (the data are $d$-dimensional vectors). Re-auditing the whole statement shows the
--   same collapse for every $d\ge1$ when $\Sigma=0$ (data identically zero a.s., which is
--   sub-Gaussian with any $\sigma>0$): then $A=0$, $T_{\lambda_n}(\hat\Sigma)=0$, the printed event
--   $|\!|\!|0-0|\!|\!|_2\ge0$ is certain and the printed inequality fails for large $n$. This is a
--   degenerate failure of the **printed source**: its proof bounds
--   $\mathbb P[|\!|\!|\hat\Sigma-\Sigma|\!|\!|_{\max}\ge\lambda_n/2]$ and uses the entrywise bound
--   $|T_{\lambda_n}(\hat\Sigma)-\Sigma|\le\frac32\lambda_nA$ on the complement, which yields the printed
--   (non-strict) event exactly when $A\ne0$. The hypothesis `hSig : Sig ≠ 0` (which also implies
--   $d\ge1$) excludes precisely this degenerate instance. As before, "i.i.d." is `iIndepFun` plus
--   `IdentDistrib` against a reference index, the mean-zero, covariance and sub-Gaussian
--   (explicit MGF bound) hypotheses are stated at the reference index, and $A$ and
--   $T_{\lambda_n}$ are the mission's definitions.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 181 (PDF p. 201), Theorem 6.23, Eq. (6.53) — with d ≥ 1 and the tacit non-degeneracy Σ ≠ 0 made explicit; the printed statement fails for Σ = 0 (data identically zero)

import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_thresholdMatrix
import Definitions.Def_HighDimStat_RandomMatrices_adjacencyMatrix
import Definitions.Def_HighDimStat_RandomMatrices_opNorm
import Definitions.Def_HighDimStat_RandomMatrices_sampleCovariance

open MeasureTheory ProbabilityTheory

namespace HighDimStat.RandomMatrices

/-- **Theorem 6.23** (Thresholding-based covariance estimation), Wainwright, *High-Dimensional
Statistics* (2019), p. 181, Eq. (6.53). Let `{xᵢ}` be an i.i.d. sequence of zero-mean random
vectors in `ℝ^d` (`d ≥ 1`) with a **nonzero** covariance matrix `Σ`, and suppose each
component `x_{ij}` is sub-Gaussian with parameter at most `σ`. If `n > log d`, then for any
`δ > 0`, the thresholded sample covariance matrix `Tλn(Σ̂)` with `λn/σ² = 8√(log d/n) + δ`
satisfies `P[|||Tλn(Σ̂)-Σ|||₂ ≥ 2|||A|||₂λn] ≤ 8e^{-(n/16)min{δ,δ²}}`, where `A` is the
adjacency matrix of the sparsity graph of `Σ`.

Corrections: (i) the retired version allowed `d = 0`, where `Real.log 0 = 0` makes `n > log d`
vacuous and both operator norms on `ℝ⁰` vanish, so the event `0 ≤ 0` is certain; (ii) to the
printed source: the same collapse happens for every `d ≥ 1` when `Σ = 0` (data identically
zero a.s., which is sub-Gaussian with any `σ > 0`): then `A = 0`, `Tλn(Σ̂) = 0`, the event
`|||0 − 0|||₂ ≥ 0` is certain, and the printed inequality fails for `n` large. The book's proof
bounds `P[|||Σ̂ − Σ|||_max ≥ λn/2]` and then uses `|Tλn(Σ̂) − Σ| ≤ (3/2)λn A` entrywise on the
complement, which yields the printed non-strict event exactly when `A ≠ 0`, i.e. `Σ ≠ 0`; the
hypothesis `hSig : Sig ≠ 0` (which also forces `d ≥ 1`) therefore excludes precisely the
degenerate instance. -/
theorem thresholded_covariance_estimation_bound_v2 {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (x : Fin n → Ω → Fin d → ℝ)
    (Sig : Matrix (Fin d) (Fin d) ℝ) (σ : ℝ) (hn0 : 0 < n) (hd : 1 ≤ d) (hSig : Sig ≠ 0)
    (hIndep : iIndepFun x Prob)
    (hIdent : ∀ i, IdentDistrib (x i) (x ⟨0, hn0⟩) Prob Prob)
    (hMean0 : ∀ j, ∫ ω, x ⟨0, hn0⟩ ω j ∂Prob = 0)
    (hCov : ∀ j k, ∫ ω, x ⟨0, hn0⟩ ω j * x ⟨0, hn0⟩ ω k ∂Prob = Sig j k)
    (hSubG : ∀ j, ∀ lam' : ℝ, Integrable (fun ω => Real.exp (lam' * x ⟨0, hn0⟩ ω j)) Prob ∧
      ∫ ω, Real.exp (lam' * x ⟨0, hn0⟩ ω j) ∂Prob ≤ Real.exp (σ ^ 2 * lam' ^ 2 / 2))
    (hnd : Real.log d < n)
    (δ : ℝ) (hδ : 0 < δ) (lam : ℝ)
    (hlam : lam / σ ^ 2 = 8 * Real.sqrt (Real.log d / n) + δ) :
    Prob.real {ω | 2 * opNorm (adjacencyMatrix Sig) * lam ≤
      opNorm (thresholdMatrix lam (sampleCovariance (fun i => x i ω)) - Sig)} ≤
      8 * Real.exp (-((n : ℝ) / 16) * min δ (δ ^ 2)) := by sorry

end HighDimStat.RandomMatrices
