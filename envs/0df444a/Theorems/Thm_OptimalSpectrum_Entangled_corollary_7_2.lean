-- Prove2me | Theorems.Thm_OptimalSpectrum_Entangled_corollary_7_2
-- name    : OptimalSpectrum.Entangled.corollary_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:25:27.521506+00:00
-- url     : https://prove2.me/theorems/e118b498-55e3-41fe-bc93-f6a544d0192d
-- title:
--   Corollary 7.2 — variance bounds for the Chebyshev moment estimates
-- statement:
--   Under the setting of Lemma 7.1 ($\sigma=\overline\Pi\rho\overline\Pi$, $L>0$, $0\preceq\sigma\preceq LI_d$), for $1\le k\le n$ and either measurement scheme,
--
--   $$\mathrm{Var}(\widehat F_{\phi_k})\le\sum_{r=1}^k\frac{c_r}{\binom nr}\Big(\frac{(4k^2/L)^r}{(2r)!}\Big)^2,\qquad \mathrm{Var}(\widehat F_{\psi_k})\le\sum_{r=1}^k\frac{c_r}{\binom nr}\Big(\frac{(2k/L)^r}{r!}\Big)^2,$$
--
--   with $c_r$ from Eq. (35). These are the variance inputs to Propositions 6.1 and 6.2 in the proof of the main theorems.
--
--   Differences from the source:
--   - reading: Var(F̂_p) for the entangled scheme → tr(F_p² ρ^⊗n) − tr(F_p ρ^⊗n)²; reason: the paper's formula for the variance of measuring an observable (pp. 6, 24)
--   - encoding: "the conditioned uniform POVM" and its i.i.d. estimators X_i → independent outcomes U_i with law (1 − tr σ)δ_0 + d⟨u|σ|u⟩U(du), X_i = X(U_i), and the variance of g_p(X_1,…,X_n); reason: the discarded outcome is recorded as the zero vector; this is the law of §7.1–7.1.1
--   - encoding: σ = Π̄ρΠ̄ with L > 0 and 0 ⪯ σ ⪯ L I_d fixed once at the start of §7 → an orthogonal projector Pbar, a density matrix ρ, L > 0 and L·I − Pbar ρ Pbar ⪰ 0 as binders; reason: standing setting of §7; 0 ⪯ σ and tr σ ≤ 1 follow
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Corollary 7.2, p. 20 (PDF p. 22)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_OptimalSpectrum_Entangled_phiPoly
import Definitions.Def_OptimalSpectrum_Entangled_psiPoly
import Definitions.Def_OptimalSpectrum_Entangled_condUniformX
import Definitions.Def_OptimalSpectrum_Entangled_gPoly
import Definitions.Def_OptimalSpectrum_Entangled_IsCondUniformSample
import Definitions.Def_OptimalSpectrum_Entangled_entVar
import Definitions.Def_OptimalSpectrum_Entangled_cCoef

open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder

namespace OptimalSpectrum.Entangled

/-- **Corollary 7.2 (Chebyshev moment variance bounds).**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Corollary 7.2, printed p. 20 (PDF p. 22): "For 1 ⩽ k ⩽ n and either measurement scheme,
Var(F̂_(ϕ_k)) ⩽ ∑_(r=1)^k (c_r/(n choose r)) ((4k²/L)^r/(2r)!)², Var(F̂_(ψ_k)) ⩽ ∑_(r=1)^k
(c_r/(n choose r)) ((2k/L)^r/r!)², where c_r is given by Eq. (35)."

Setting of §7 as in Lemma 7.1: `σ = Π̄ρΠ̄`, `L > 0`, `0 ⪯ σ ⪯ LI_d`; `ϕ_k`, `ψ_k` are Eqs. (20),
(22), polynomials of degree `k`.
1. Unentangled scheme, both bounds.
2. Entangled scheme, both bounds.

**Formalization Note.** Both schemes are stated; the goal theorem uses the entangled one. -/
theorem corollary_7_2 (d n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) (L : ℝ) (hL : 0 < L)
    (Pbar ρ : Matrix (Fin d) (Fin d) ℂ) (hP : Pbar.IsHermitian) (hP2 : Pbar * Pbar = Pbar)
    (hρ : QAlgorithms.IsDensityMatrix ρ)
    (hσL : ((L : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - Pbar * ρ * Pbar).PosSemidef) :
    (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (U : Fin n → Ω → EuclideanSpace ℂ (Fin d)),
        IsCondUniformSample P (Pbar * ρ * Pbar) U →
        variance (fun ω => gPoly d n (phiPoly L k) fun i => condUniformX d (U i ω)) P ≤
            ∑ r ∈ Finset.Icc 1 k, cCoef Scheme.unentangled d L r / (n.choose r : ℝ) * ((4 * (k : ℝ) ^ 2 / L) ^ r / (2 * r).factorial) ^ 2 ∧
          variance (fun ω => gPoly d n (psiPoly L k) fun i => condUniformX d (U i ω)) P ≤
            ∑ r ∈ Finset.Icc 1 k, cCoef Scheme.unentangled d L r / (n.choose r : ℝ) * ((2 * (k : ℝ) / L) ^ r / r.factorial) ^ 2) ∧
    entVar d n Pbar (phiPoly L k) ρ ≤
        ∑ r ∈ Finset.Icc 1 k, cCoef Scheme.entangled d L r / (n.choose r : ℝ) * ((4 * (k : ℝ) ^ 2 / L) ^ r / (2 * r).factorial) ^ 2 ∧
    entVar d n Pbar (psiPoly L k) ρ ≤
        ∑ r ∈ Finset.Icc 1 k, cCoef Scheme.entangled d L r / (n.choose r : ℝ) * ((2 * (k : ℝ) / L) ^ r / r.factorial) ^ 2 := by sorry

end OptimalSpectrum.Entangled
