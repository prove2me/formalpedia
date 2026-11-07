-- Prove2me | Theorems.Thm_OptimalSpectrum_Entangled_lemma_7_1
-- name    : OptimalSpectrum.Entangled.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:25:06.565647+00:00
-- url     : https://prove2.me/theorems/8459fa62-44eb-4fdc-b2a4-9582acdee969
-- title:
--   Lemma 7.1 — polynomial variance bound for both schemes
-- statement:
--   Let $1\le k\le n$, let $p$ be a real polynomial of degree at most $k$, let $\sigma=\overline\Pi\rho\overline\Pi$ for an orthogonal projector $\overline\Pi$ and a density matrix $\rho$, and let $L>0$ with $0\preceq\sigma\preceq LI_d$. For either measurement scheme,
--
--   $$\mathrm{Var}(\widehat F_p)\le\sum_{r=1}^k\frac{c_r}{\binom nr}\Big(\frac{\|p^{(r)}\|_{\infty,[0,L]}}{r!}\Big)^2,\tag{34}$$
--
--   where for $r\ge1$
--
--   $$c_r=\frac1{(r-1)!}\cdot\begin{cases}3^r d^{\uparrow r},&\text{unentangled},\\ \prod_{j=0}^{r-1}(1+jL),&\text{entangled}.\end{cases}\tag{35}$$
--
--   Both clauses are stated: the unentangled one for $n$ i.i.d. conditioned-uniform outcomes, the entangled one for the measurement of $F_p$ on $\rho^{\otimes n}$.
--
--   Differences from the source:
--   - reading: Var(F̂_p) for the entangled scheme → tr(F_p² ρ^⊗n) − tr(F_p ρ^⊗n)²; reason: the paper's formula for the variance of measuring an observable (pp. 6, 24)
--   - encoding: "the conditioned uniform POVM" and its i.i.d. estimators X_i → independent outcomes U_i with law (1 − tr σ)δ_0 + d⟨u|σ|u⟩U(du), X_i = X(U_i), and the variance of g_p(X_1,…,X_n); reason: the discarded outcome is recorded as the zero vector; this is the law of §7.1–7.1.1
--   - encoding: σ = Π̄ρΠ̄ with L > 0 and 0 ⪯ σ ⪯ L I_d fixed once at the start of §7 → an orthogonal projector Pbar, a density matrix ρ, L > 0 and L·I − Pbar ρ Pbar ⪰ 0 as binders; reason: standing setting of §7; 0 ⪯ σ and tr σ ≤ 1 follow
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Lemma 7.1, Eqs. (34)–(35), pp. 19–20 (PDF pp. 21–22)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_OptimalSpectrum_Entangled_supNormDeriv
import Definitions.Def_OptimalSpectrum_Entangled_condUniformX
import Definitions.Def_OptimalSpectrum_Entangled_gPoly
import Definitions.Def_OptimalSpectrum_Entangled_IsCondUniformSample
import Definitions.Def_OptimalSpectrum_Entangled_entVar
import Definitions.Def_OptimalSpectrum_Entangled_cCoef

open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder

namespace OptimalSpectrum.Entangled

/-- **Lemma 7.1 (Polynomial variance bound).**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Lemma 7.1, printed pp. 19–20 (PDF pp. 21–22): "Let 1 ⩽ k ⩽ n and let p be a polynomial of
degree at most k. For either measurement scheme, Var(F̂_p) ⩽ ∑_(r=1)^k (c_r/(n choose r))
(∥p^(r)∥_(∞,[0,L])/r!)², (34) where, for r ⩾ 1, c_r := (1/(r − 1)!) · {3^r d^↑r, unentangled;
∏_(j=0)^(r−1)(1 + jL), entangled.} (35)"

Setting of §7 (printed p. 19): `Π̄` the small-bucket projector, `σ = Π̄ρΠ̄` with `ρ` a density
matrix, and `L > 0` with `0 ⪯ σ ⪯ LI_d`.
1. Unentangled: `F̂_p = g_p(X₁, …, X_n)` for `n` i.i.d. conditioned-uniform outcomes.
2. Entangled: `F̂_p` is the measured value of `F_p` in `ρ^{⊗n}`.

**Formalization Note.** `0 ⪯ σ` and `tr σ ≤ 1` hold automatically for `σ = Π̄ρΠ̄`. Both clauses of the
lemma are stated; the goal theorem uses the entangled one. -/
theorem lemma_7_1 (d n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) (L : ℝ) (hL : 0 < L)
    (Pbar ρ : Matrix (Fin d) (Fin d) ℂ) (hP : Pbar.IsHermitian) (hP2 : Pbar * Pbar = Pbar)
    (hρ : QAlgorithms.IsDensityMatrix ρ)
    (hσL : ((L : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - Pbar * ρ * Pbar).PosSemidef) (p : Polynomial ℝ) (hp : p.natDegree ≤ k) :
    (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (U : Fin n → Ω → EuclideanSpace ℂ (Fin d)),
        IsCondUniformSample P (Pbar * ρ * Pbar) U →
        variance (fun ω => gPoly d n p fun i => condUniformX d (U i ω)) P ≤
          ∑ r ∈ Finset.Icc 1 k, cCoef Scheme.unentangled d L r / (n.choose r : ℝ) *
            (supNormDeriv p r L / r.factorial) ^ 2) ∧
    entVar d n Pbar p ρ ≤
      ∑ r ∈ Finset.Icc 1 k, cCoef Scheme.entangled d L r / (n.choose r : ℝ) *
        (supNormDeriv p r L / r.factorial) ^ 2 := by sorry

end OptimalSpectrum.Entangled
