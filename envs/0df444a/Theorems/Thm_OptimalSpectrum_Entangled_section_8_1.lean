-- Prove2me | Theorems.Thm_OptimalSpectrum_Entangled_section_8_1
-- name    : OptimalSpectrum.Entangled.section_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:23:40.953379+00:00
-- url     : https://prove2.me/theorems/e4579fc5-3427-4f5b-8e5f-62dbd19f42c0
-- title:
--   §8.1 — conditional expected error $O(\varepsilon)$ and copy count under Tables 2–3
-- statement:
--   There are universal constants $A,b,C>0$ such that for every $d\ge3$, $0<\varepsilon\le1/10$ and either scheme ($D=1$ entangled, $D=d$ unentangled), with $\ell=\log d$ and the parameters of Table 3,
--
--   | regime | $p_k$ | $K$ | $B$ |
--   |---|---|---|---|
--   | $\varepsilon\ell>1$ | $\phi_k$ | $\lceil\ell^2\rceil$ | $b\varepsilon^2K^2/(1.1d)$ |
--   | $\varepsilon\ell\le1$ | $\psi_k$ | $\lceil\ell^2/\varepsilon\rceil$ | $\ell^2/(1.1d)$ |
--
--   $L=1.1B$ and $n=\lceil A\,dD/(L\varepsilon^2)\rceil$:
--
--   1. $B<1$;
--   2. $K\le n/2$;
--   3. $n\le C\,d^2D\min\{(\varepsilon\ell)^{-4},(\varepsilon\ell)^{-2}\}$;
--   4. for every spectrum $\alpha\in Z_d$ and all unbiased moment estimates with finite variances whose variances obey the bounds of Corollary 7.2 for the scheme, every measurable least-squares estimator $\widehat z$ satisfies
--   $$\mathbb E\,d_{\mathrm{TV}}(\alpha,\widehat z)\le C\varepsilon .$$
--
--   This is the parameter calculus that turns Propositions 6.1–6.2 and Corollary 7.2 into the copy bounds of Theorems 1.1 and 1.3.
--
--   Differences from the source:
--   - generalization: conditional on a successful bucketing output, the quantum moment estimates of §7.1 for σ, error of ẑ is O(ε) → the bound for every α ∈ Z_d and every unbiased finite-variance estimate family satisfying the variance bounds of Corollary 7.2; reason: these are the only properties of the quantum stage the paragraph uses; the quantum estimates satisfy them (Eq. (39), Corollary 7.2), so the page's claim is a special case
--   - encoding: O(ε) and O(d²D min{…}) with constants A large, b small → ∃ A b C > 0 before d, ε and the scheme; reason: universal constants, as on the page
--   - encoding: ℓ = log d, base unstated; 1.1 → Real.log; 11/10; reason: the base changes only constants
--   - encoding: E d_TV(ẑ, spec σ) for ẑ ∈ arg min → measurable selections ẑ; reason: the expectation is undefined otherwise
--   - generalization: the sentence "the conditional expected error of ẑ is O(ε)" → also the clauses B < 1 and K ⩽ n/2 (proved in the Full-interval and Interior paragraphs) and n ⩽ C d²D min{…} (Copy complexity paragraph); reason: these are claims of §8.1 itself, conjoined; dropping them gives the error claim
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §8.1 (unnumbered), pp. 26–28 (PDF pp. 28–30), Tables 2–3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38
import Definitions.Def_OptimalSpectrum_Entangled_phiPoly
import Definitions.Def_OptimalSpectrum_Entangled_psiPoly
import Definitions.Def_OptimalSpectrum_Entangled_Zd
import Definitions.Def_OptimalSpectrum_Entangled_momentVar
import Definitions.Def_OptimalSpectrum_Entangled_IsUnbiasedMoments
import Definitions.Def_OptimalSpectrum_Entangled_IsLSEstimator
import Definitions.Def_OptimalSpectrum_Entangled_Scheme
import Definitions.Def_OptimalSpectrum_Entangled_cCoef

open MeasureTheory
open QAlgorithms.Papers.Independent.Support50.P38 (tv)

namespace OptimalSpectrum.Entangled

/-- **§8.1: conditional expected error under the parameters of Tables 2–3.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §8.1 (unnumbered), printed pp. 26–28 (PDF pp. 28–30): "Write D = 1 for entangled measurements
and D = d for unentangled measurements. Use the parameters in Tables 2 and 3, with L = 1.1B. Set
n = ⌈A dD/(Lε²)⌉ … Condition on any successful bucketing output, so that 0 ⪯ σ ⪯ LI_d and tr(σ) ⩽ 1.
We first show that the conditional expected error of ẑ is O(ε)." Algorithm 8.1 (printed p. 27) fixes
`d ≥ 3`, `0 < ε ⩽ 1/10`, `ℓ = log d`, and Table 3 (printed p. 26) sets: if `εℓ > 1`, `p_k = ϕ_k`,
`K = ⌈ℓ²⌉`, `B = bε²K²/(1.1d)`; if `εℓ ⩽ 1`, `p_k = ψ_k`, `K = ⌈ℓ²/ε⌉`, `B = ℓ²/(1.1d)`.

There are universal constants `A, b, C > 0` such that for every `d ≥ 3`, `ε ∈ (0, 1/10]` and scheme,
with these parameters:
1. `B < 1` (needed by the bucketing guarantees);
2. `K ≤ n/2` (written `2K ≤ n`);
3. `n ≤ C d² D min{(εℓ)⁻⁴, (εℓ)⁻²}` (the copy-complexity paragraph, printed p. 28);
4. for every spectrum `α ∈ Z_d` and every family of unbiased moment estimates with finite variances
   whose variances satisfy the bounds of Corollary 7.2 for the scheme (with `c_r` of Eq. (35)), every
   measurable least-squares estimator `ẑ` (Algorithm 8.1, step 3) has `E d_TV(α, ẑ) ≤ Cε`.

**Formalization Note.** The quantum measurement is abstracted into its two consequences used on
these pages: unbiasedness and the variance bound of Corollary 7.2. `log` is the natural logarithm;
`1.1` is `11/10`. -/
theorem section_8_1 :
    ∃ A b C : ℝ, 0 < A ∧ 0 < b ∧ 0 < C ∧
      ∀ d : ℕ, 3 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 → ∀ s : Scheme,
        let ℓ : ℝ := Real.log d
        let D : ℝ := if s = Scheme.entangled then 1 else (d : ℝ)
        let K : ℕ := if 1 < ε * ℓ then ⌈ℓ ^ 2⌉₊ else ⌈ℓ ^ 2 / ε⌉₊
        let B : ℝ :=
          if 1 < ε * ℓ then b * ε ^ 2 * (K : ℝ) ^ 2 / (11 / 10 * d) else ℓ ^ 2 / (11 / 10 * d)
        let L : ℝ := 11 / 10 * B
        let q : ℕ → Polynomial ℝ := fun k => if 1 < ε * ℓ then phiPoly L k else psiPoly L k
        let v : ℕ → ℕ → ℝ := fun k r =>
          if 1 < ε * ℓ then (4 * (k : ℝ) ^ 2 / L) ^ r / (2 * r).factorial
          else (2 * (k : ℝ) / L) ^ r / r.factorial
        let n : ℕ := ⌈A * d * D / (L * ε ^ 2)⌉₊
        B < 1 ∧ 2 * K ≤ n ∧
          (n : ℝ) ≤ C * (d : ℝ) ^ 2 * D * min (1 / (ε * ℓ) ^ 4) (1 / (ε * ℓ) ^ 2) ∧
          ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
            (α : Fin d → ℝ) (Mhat : ℕ → Ω → ℝ) (zhat : Ω → Fin d → ℝ),
            α ∈ Zd d L → IsUnbiasedMoments μ K Mhat α →
            (∀ k, 1 ≤ k → k ≤ K →
              momentVar μ d K Mhat α (q k) ≤
                ∑ r ∈ Finset.Icc 1 k, cCoef s d L r / (n.choose r : ℝ) * v k r ^ 2) →
            IsLSEstimator d L K Mhat q zhat → Measurable zhat →
            ∫ ω, tv α (zhat ω) ∂μ ≤ C * ε := by sorry

end OptimalSpectrum.Entangled
