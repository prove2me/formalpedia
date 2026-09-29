-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities
-- name    : LanglandsTunnell.Converse.exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/5acb81ed-d912-5eb9-a354-5d2a43853473
-- title:
--   Assembling archimedean Rankin–Selberg integrals from diagonal torus identities
-- statement:
--   Give $\mathrm{GL}_2(\mathbb{R})$ its Borel $\sigma$-algebra and let [`RSCarrier.archMeasure`](def/LanglandsTunnell_RSCarrierSplit.html#L11) be the measure obtained by pulling back Lebesgue measure on $2\times 2$ real matrices along the inclusion and weighting it by $|\det g|^{-2}$; assume it is a Haar measure, and let $\mu_N$ be a Haar measure on the subgroup $N$ of $\mathrm{GL}_2(\mathbb{R})$ given by the image of the unipotent homomorphism $x \mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$. Then there is a constant $c>0$, depending only on these two measures, such that for every $n$, every $\mathrm{coef} : \mathrm{Fin}\,n \to \mathbb{C}$, every two families of pairs of functions $W_i,F_i$ and $\widetilde W_i,\widetilde F_i$ on $\mathrm{GL}_2(\mathbb{R})$, all functions $\Gamma,\widetilde\Gamma,e,\widetilde e : \mathbb{C}\to\mathbb{C}$, every $\varepsilon\in\mathbb{C}$ and every $\sigma_0\in\mathbb{R}$, the following holds. Assume: each product $W_iF_i$ and $\widetilde W_i\widetilde F_i$ is invariant under left translation by elements of $N$, and under right translation by those $k$ with $\det k = 1$ lying in the subgroup of $k$ with $\|\det k\|=1$ for which $(x,y)\mapsto (xk_{00}+yk_{10},\,xk_{01}+yk_{11})$ preserves $\|x\|^2+\|y\|^2$; all four functions in each index are measurable; for each $i$ and each $s$ with $\operatorname{Re} s > \sigma_0$ the functions $g\mapsto (W_ig)(F_ig)\,|\det g|^{s-1/2}$ and $g\mapsto (\widetilde W_ig)(\widetilde F_ig)\,|\det g|^{s-1/2}$ are integrable for `archMeasure` weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of $N$ attached to $\mu_N$; for $\operatorname{Re} s>\sigma_0$ the weighted diagonal torus sums $\sum_i \mathrm{coef}_i \int_{a_2>0}\int_{a_1\in\mathbb{R}} (W_ip)(F_ip)|\det p|^{s-1/2}a_1^{-2}$, with $p=\mathrm{diag}(a_1,a_2)$ and the integrand set to $0$ unless $a_1\neq 0$ and $a_2>0$, equal $e(s)\Gamma(s)$, and the corresponding sums for $\widetilde W_i,\widetilde F_i$ equal $\widetilde e(s)\widetilde\Gamma(s)$; and $\widetilde e(s)=\varepsilon\, e(1-s)$ for all $s$. The conclusion is that for $\operatorname{Re} s>\sigma_0$ one has $\sum_i \mathrm{coef}_i\, \mathrm{rsArchIntegral}(\mathrm{archMeasure},\mu_N,s,W_i,F_i) = c\,e(s)\Gamma(s)$ and likewise $\sum_i \mathrm{coef}_i\,\mathrm{rsArchIntegral}(\mathrm{archMeasure},\mu_N,s,\widetilde W_i,\widetilde F_i) = c\,\widetilde e(s)\widetilde\Gamma(s)$, and that $c\,\widetilde e(s) = \varepsilon\,(c\,e(1-s))$ for all $s$.
--
--   This is the archimedean Iwasawa-type reduction in the Rankin–Selberg theory used for the converse theorem input to Langlands–Tunnell: identities for integrals over the diagonal torus, with the measure factor $a_1^{-2}\,da_1\,da_2$, are transported by linearity to identities for the archimedean Rankin–Selberg integrals $\mathrm{rsArchIntegral}$, at the cost of a single positive constant that is uniform in the data and depends only on the two Haar measures; the $L$-factors $\Gamma,\widetilde\Gamma$, the elementary factors $e,\widetilde e$ and $\varepsilon$ are unconstrained apart from the displayed identities. It feeds the analytic continuation, non-vanishing and boundedness statements about the archimedean Rankin–Selberg integral in this development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities.lean

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier

theorem LanglandsTunnell.Converse.exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (_hHaar : RSCarrier.archMeasure.IsHaarMeasure)
      (μN : Measure realUnipotent) [μN.IsHaarMeasure],
    ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (coef : Fin n → ℂ)
      (W F Wd Fd : Fin n → GL (Fin 2) ℝ → ℂ) (Γ Γd e ed : ℂ → ℂ) (ε : ℂ) (σ₀ : ℝ)
      (_hN : ∀ i, ∀ u ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ,
        W i (u * g) * F i (u * g) = W i g * F i g)
      (_hNd : ∀ i, ∀ u ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ,
        Wd i (u * g) * Fd i (u * g) = Wd i g * Fd i g)
      (_hK : ∀ i, ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
        ∀ g : GL (Fin 2) ℝ, W i (g * k) * F i (g * k) = W i g * F i g)
      (_hKd : ∀ i, ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
        ∀ g : GL (Fin 2) ℝ, Wd i (g * k) * Fd i (g * k) = Wd i g * Fd i g)
      (_hmeas : ∀ i, Measurable (W i) ∧ Measurable (F i) ∧ Measurable (Wd i) ∧ Measurable (Fd i))
      (_hint : ∀ i (s : ℂ), σ₀ < s.re → Integrable
        (fun g : GL (Fin 2) ℝ =>
          (W i g * F i g) * (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
        (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μN)))
      (_hintd : ∀ i (s : ℂ), σ₀ < s.re → Integrable
        (fun g : GL (Fin 2) ℝ =>
          (Wd i g * Fd i g) * (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
        (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μN)))
      (_hvec : ∀ s : ℂ, σ₀ < s.re →
        ∑ i, coef i *
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if h : a₁ ≠ 0 ∧ 0 < a₂ then
                let p : GL (Fin 2) ℝ := upperUnit a₁ 0 a₂ h.1 h.2.ne'
                ((W i p * F i p) * (((|(Matrix.GeneralLinearGroup.det p : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
          = e s * Γ s)
      (_hpair : ∀ s : ℂ, σ₀ < s.re →
        ∑ i, coef i *
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if h : a₁ ≠ 0 ∧ 0 < a₂ then
                let p : GL (Fin 2) ℝ := upperUnit a₁ 0 a₂ h.1 h.2.ne'
                ((Wd i p * Fd i p) * (((|(Matrix.GeneralLinearGroup.det p : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
          = ed s * Γd s)
      (_hfe : ∀ s : ℂ, ed s = ε * e (1 - s)),
      (∀ s : ℂ, σ₀ < s.re →
          ∑ i, coef i * rsArchIntegral RSCarrier.archMeasure μN s (W i) (F i) = (c : ℂ) * (e s * Γ s)) ∧
        (∀ s : ℂ, σ₀ < s.re →
          ∑ i, coef i * rsArchIntegral RSCarrier.archMeasure μN s (Wd i) (Fd i) =
            (c : ℂ) * (ed s * Γd s)) ∧
        (∀ s : ℂ, (c : ℂ) * ed s = ε * ((c : ℂ) * e (1 - s))) := by sorry
