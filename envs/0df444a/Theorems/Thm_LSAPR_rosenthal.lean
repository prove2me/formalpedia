-- Prove2me | Theorems.Thm_LSAPR_rosenthal
-- name    : LSAPR.rosenthal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:22.017313+00:00
-- url     : https://prove2.me/theorems/21ee70ca-79f6-430a-91ee-e9d6956665d5
-- title:
--   Rosenthal's inequality with $\mathrm C_{\mathrm{Rm},1}=60\mathrm e$, $\mathrm C_{\mathrm{Rm},2}=60$ for independent centered random vectors (Pinelis)
-- statement:
--   Let $X_1,\dots,X_m$ be independent centered random vectors of $\mathbb R^d$ with $\mathbb E[\|X_i\|^2]\le s^2$, $s\ge0$. Then for every real $p\ge2$,
--   $$\mathbb E^{1/p}\Big[\Big\|\sum_{i=1}^mX_i\Big\|^p\Big]\le\mathrm C_{\mathrm{Rm},1}p^{1/2}m^{1/2}s+\mathrm C_{\mathrm{Rm},2}\,p\,\mathbb E^{1/p}\big[\max_i\|X_i\|^p\big],$$
--   with $\mathrm C_{\mathrm{Rm},1}=60\mathrm e$ and $\mathrm C_{\mathrm{Rm},2}=60$.
--
--   In the proof of Theorem 2 this bounds the leading term $\sum_{t=n/2}^{n-1}\varepsilon(Z_{t+1})$, and the factor $p^{1/2}$ of the Gaussian part becomes the leading term of Theorem 1.
--
--   Differences from the source:
--   - generalization: the instance m = n/2, X = ε(Z_{t+1}), s² = Tr Σ_ε → any independent centered family with E‖Xᵢ‖² ≤ s²; reason: the page's instance satisfies these hypotheses, since E‖ε(Z)‖² = Tr Σ_ε
--   - encoding: E^{1/p}[‖X‖^p] of a nonnegative or vector quantity → eLpNorm X (ENNReal.ofReal p) P in ℝ≥0∞; reason: same value, and an infinite moment would falsify the bound rather than make it vacuous
-- source:
--   Durmus, Moulines, Naumov & Samsonov, Finite-time High-probability Bounds for Polyak-Ruppert Averaged Iterates of Linear Stochastic Approximation, arXiv:2207.04475v2, proof of Theorem 2, p.19 (Rosenthal, Pinelis 1994, Theorem 4.1); constants, table p.16

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_LSAPR_Model

open MeasureTheory ProbabilityTheory PolyakJuditsky.Averaging

namespace LSAPR

/-- The Rosenthal inequality (Pinelis 1994, Theorem 4.1) as used in the proof of Theorem 2,
arXiv:2207.04475v2, p.19, with `C_{Rm,1} = 60 e`, `C_{Rm,2} = 60` (table, p.16): for independent
centered `ℝ^d`-valued `X₁, …, X_m` with `E[‖X_i‖²] ≤ s²` and real `p ≥ 2`,
`E^{1/p}[‖∑ X_i‖^p] ≤ C_{Rm,1} p^{1/2} m^{1/2} s + C_{Rm,2} p E^{1/p}[max_i ‖X_i‖^p]`.

**Formalization Note.** The page has `m = n/2`, `X_i = ε(Z_{t+1})`, `s² = Tr Σ_ε`. -/
theorem rosenthal {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin m → Ω → Vec d) (s : ℝ) (hs : 0 ≤ s)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hvar : ∀ i, ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ s ^ 2) (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (fun ω => ∑ i, X i ω) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (CRm1 * Real.sqrt p * Real.sqrt m * s)
        + ENNReal.ofReal (CRm2 * p) *
          eLpNorm (fun ω => Finset.univ.sup fun i => ‖X i ω‖₊) (ENNReal.ofReal p) P := by sorry

end LSAPR
