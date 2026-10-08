-- Prove2me | Theorems.Thm_OptimalRLS_Upper_theorem_4
-- name    : OptimalRLS.Upper.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:25:57.006828+00:00
-- url     : https://prove2.me/theorems/893210e9-6dcc-42dd-bb6d-019f1d96ec0b
-- title:
--   Theorem 4, p. 14 — w.p. ≥ 1 − η, E[f_z^λ] − E[f_H] is bounded by A, B, N(λ) (constant corrected to 3C_η)
-- statement:
--   Assume Hypothesis 1 with constant $\kappa$, and let $\rho$ satisfy Hypothesis 2 with constants $M,\Sigma$, where $f_{\mathcal H}$ is the minimizer of minimal norm. Let $(e_i,t_i)$ be the eigen-system (16) of $T$. Let $\ell\ge1$, $\lambda>0$ and $0<\eta<1$, and put $C_\eta=32\log^2(6/\eta)$. Write $f^\lambda$ for the minimizer of the regularized expected risk, $f_{\mathbf z}^\lambda$ for the RLS estimator on $\mathbf z\in Z^\ell$, and
--   $$\mathcal A(\lambda)=\mathcal E[f^\lambda]-\mathcal E[f_{\mathcal H}],\qquad\mathcal B(\lambda)=\|f^\lambda-f_{\mathcal H}\|_{\mathcal H}^2,\qquad\mathcal N(\lambda)=\sum_i\frac{t_i}{t_i+\lambda}.$$
--   If
--   $$\ell\ge\frac{2C_\eta\kappa\mathcal N(\lambda)}{\lambda}\qquad\text{and}\qquad\lambda\le\|T\|_{\mathcal L(\mathcal H)},\tag{35}$$
--   then, with probability at least $1-\eta$ over $\mathbf z\sim\rho^\ell$,
--   $$\mathcal E[f_{\mathbf z}^\lambda]-\mathcal E[f_{\mathcal H}]\le3C_\eta\Big(\mathcal A(\lambda)+\frac{\kappa^2\mathcal B(\lambda)}{\ell^2\lambda}+\frac{\kappa\mathcal A(\lambda)}{\ell\lambda}+\frac{\kappa M^2}{\ell^2\lambda}+\frac{\Sigma^2\mathcal N(\lambda)}{\ell}\Big).$$
--
--   This non-asymptotic bound separates the approximation terms $\mathcal A,\mathcal B$, which depend on $f_{\mathcal H}$, from the complexity term $\mathcal N(\lambda)$, which depends on $\rho_X$; Theorem 1 follows by bounding these over $\mathcal P(b,c)$ and choosing $\lambda=\lambda_\ell$.
--
--   **Formalization Note** The paper prints the factor $C_\eta$ in (34). Its proof gives $\mathcal E[f_{\mathbf z}^\lambda]-\mathcal E[f_{\mathcal H}]\le3(\mathcal A+\mathcal S_1+\mathcal S_2)$ by (36), with $\mathcal S_2\le8\log^2(6/\eta)(4\kappa^2\mathcal B/(\ell^2\lambda)+\kappa\mathcal A/(\ell\lambda))$ by (44) and $\mathcal S_1\le32\log^2(6/\eta)(\kappa M^2/(\ell^2\lambda)+\Sigma^2\mathcal N/\ell)$ by (49); the last display on p. 18 drops the factor $3$ of (36). The corrected bound is stated with $3C_\eta$; condition (35) is kept with $C_\eta$ as printed, which is what the proof uses. "With probability greater than $1-\eta$" is stated as: the event where the inequality fails has (outer) $\rho^\ell$-measure at most $\eta$. $\lambda\le\|T\|$ is written as $\lambda\le t_i$ for some $i$ ($\|T\|=\max_it_i$). The estimator is any map $\mathbf z\mapsto f_{\mathbf z}^\lambda$ solving (18), which is unique by Proposition 1 v).
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Theorem 4, (34)–(35), p. 14; proof pp. 14–18, (36), (44), (49)

import Mathlib
import Definitions.Def_OptimalRLS_Upper_Setting

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace OptimalRLS.Upper

/-- **Theorem 4** (p. 14), with the constant corrected to `3 C_η`. Let `ρ` satisfy
Hypothesis 2 with the minimal-norm minimizer `f_H`, let `(e, t)` be an eigen-system of `T`, `ℓ ≥ 1`,
`λ > 0`, `0 < η < 1`, `C_η = 32 log²(6/η)`, and let `f^λ` minimize the regularized expected risk and
`est z = f_z^λ`. If (35) holds, `ℓ ≥ 2 C_η κ N(λ)/λ` and `λ ≤ ‖T‖` (`∃ i, λ ≤ t_i`), then the event
`E[f_z^λ] − E[f_H] > 3 C_η (A + κ²B/(ℓ²λ) + κA/(ℓλ) + κM²/(ℓ²λ) + Σ²N(λ)/ℓ)` has
`ρ^ℓ`-probability at most `η`, with `A = E[f^λ] − E[f_H]`, `B = ‖f^λ − f_H‖²_H`, `N = effDim t λ`. -/
theorem theorem_4
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H X Y]
    {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) (h1 : Hyp1 X H κ v)
    (M Sig : ℝ) (ρ : Measure (X × Y)) [IsProbabilityMeasure ρ] (fH : H)
    (hfH : IsMinNormMinimizer ρ fH) (h2 : Hyp2 M Sig ρ fH)
    {ι' : Type*} [Countable ι'] (e : ι' → H) (t : ι' → ℝ) (het : IsEigenSystem ρ.fst e t)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (lam : ℝ) (hlam : 0 < lam) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (fl : H) (hfl : ∀ f : H, regRisk ρ lam fl ≤ regRisk ρ lam f)
    (est : (Fin ℓ → X × Y) → H) (hest : ∀ z, IsRLSMin lam z (est z))
    (h35a : 2 * (32 * Real.log (6 / η) ^ 2) * κ * effDim t lam / lam ≤ (ℓ : ℝ))
    (h35b : ∃ i, lam ≤ t i) :
    let Cη : ℝ := 32 * Real.log (6 / η) ^ 2
    let A : ℝ := risk ρ fl - risk ρ fH
    let B : ℝ := ‖fl - fH‖ ^ 2
    let N : ℝ := effDim t lam
    (Measure.pi fun _ : Fin ℓ => ρ)
        {z | 3 * Cη * (A + κ ^ 2 * B / ((ℓ : ℝ) ^ 2 * lam) + κ * A / ((ℓ : ℝ) * lam)
              + κ * M ^ 2 / ((ℓ : ℝ) ^ 2 * lam) + Sig ^ 2 * N / (ℓ : ℝ))
            < risk ρ (est z) - risk ρ fH} ≤ ENNReal.ofReal η := by sorry

end OptimalRLS.Upper
