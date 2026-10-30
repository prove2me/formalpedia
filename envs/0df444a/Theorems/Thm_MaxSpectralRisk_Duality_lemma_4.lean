-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_lemma_4
-- name    : MaxSpectralRisk.Duality.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:27.827175+00:00
-- url     : https://prove2.me/theorems/50e8b684-4571-4264-a6e5-cf27e4d301e9
-- title:
--   Lemma 4, p. 9 — K_π = ∫ inf_b g_u(b, π) dΓσ = Γσ({0})E_π[L] + ∫ ES_{u,π}(L) dΓ̃σ, minimizers, and the L^∞(Γσ) infimum
-- statement:
--   Throughout, $\mathcal X$ and $\mathcal Y$ are Polish spaces with their Borel $\sigma$-algebras, $\mu$ and $\nu$ are Borel probability measures on them, $\Pi(\mu,\nu)$ is the set of couplings, $\sigma$ is a bounded, right-continuous spectral function (A.4), and $L:\mathcal X\times\mathcal Y\to\mathbb R$ is the loss. Assume A.1–A.3 and let $\pi\in\Pi(\mu,\nu)$. Let
--   $$K_\pi=\inf_{\beta}\int_0^1g_u(\beta(u),\pi)\,d\Gamma_\sigma(u),$$
--   the infimum over Borel measurable $\beta$, the integral taking values in $\mathbb R\cup\{\infty\}$. Write $\widetilde\Gamma_\sigma$ for the part of $\Gamma_\sigma$ on $(0,1)$. Then
--
--   1. $K_\pi=\int_0^1\inf_b g_u(b,\pi)\,d\Gamma_\sigma(u)=\Gamma_\sigma(\{0\})\,\mathbb E_\pi[L]+\int_0^1\mathrm{ES}_{u,\pi}(L)\,d\widetilde\Gamma_\sigma(u)$;
--   2. a Borel measurable $\beta$ attains $K_\pi$ if and only if $\beta(u)\in\operatorname{argmin}_{b\in\mathbb R}\big(b+(1-u)^{-1}\mathbb E_\pi[(L-b)_+]\big)$ for $\Gamma_\sigma$-a.e. $u\in[0,1)$;
--   3. $K_\pi=\inf_{\beta\in\mathcal L^\infty(\Gamma_\sigma)}\int_0^1g_u(\beta(u),\pi)\,d\Gamma_\sigma(u)$.
--
--   This is the interchange of infimum and integral that turns the min–max problem back into $\max_\pi R_{\pi,\sigma}(L)$ in step (9) of the proof of Theorem 1.
--
--   **Formalization Note.** Integrals of possibly non-integrable integrands are $+\infty$ (the integrands are bounded below by an integrable function). $\beta$ is a function on $\mathbb R$; only its values on $[0,1)$, where $\Gamma_\sigma$ lives, matter. $\widetilde\Gamma_\sigma=\Gamma_\sigma-z_0\delta_0$ is $\Gamma_\sigma$ restricted to $(0,1)$. The inner $\inf_b$ is a real infimum, bounded below for $u\in[0,1)$. Lemma 3 of the paper is not used and not posed.
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 9, Lemma 4 (with Remark 1 for Γ̃σ)

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting

namespace MaxSpectralRisk.Duality

open MeasureTheory Filter Topology

theorem lemma_4 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (sig : SpectralFunction) (L : X × Y → ℝ)
    (hA : Assumptions L μ ν) (π : Measure (X × Y)) (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) :
    K sig L π = extIntegral (fun u => ⨅ b : ℝ, g u b π L) (Gam sig) ∧
    K sig L π = (((Gam sig).real {0} * ∫ p, L p ∂π +
      ∫ u, ES u π L ∂((Gam sig).restrict (Set.Ioo 0 1)) : ℝ) : EReal) ∧
    (∀ β : ℝ → ℝ, Measurable β →
      (extIntegral (fun u => g u (β u) π L) (Gam sig) = K sig L π ↔
        ∀ᵐ u ∂(Gam sig), ∀ b : ℝ, g u (β u) π L ≤ g u b π L)) ∧
    K sig L π = ⨅ (β : ℝ → ℝ) (_ : MemLp β ⊤ (Gam sig)),
      extIntegral (fun u => g u (β u) π L) (Gam sig) := by sorry

end MaxSpectralRisk.Duality
