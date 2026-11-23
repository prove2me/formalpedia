-- Prove2me | Theorems.Thm_LeJEPA_anisotropy_amplifies_variance
-- name    : LeJEPA.anisotropy_amplifies_variance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:01:13.265261+00:00
-- url     : https://prove2.me/theorems/8d7281eb-2d06-4025-acbb-86164428898a
-- title:
--   Lemma 2: anisotropy amplifies the variance of the least-squares probe
-- statement:
--   Let $Z_{\rm aniso},Z_{\rm iso}\in\mathbb{R}^{N\times K}$ ($K\ge1$) have the same column span. Let $G=Z_{\rm aniso}^\top Z_{\rm aniso}$ be positive definite and not a multiple of the identity, and let $Z_{\rm iso}^\top Z_{\rm iso}=(\operatorname{tr}G/K)\,I_K$. For noise variance $\sigma^2>0$, the least-squares probe ($\lambda=0$) has strictly larger total variance on the anisotropic embedding:
--
--   $$\sigma^2\operatorname{tr}\big((Z_{\rm iso}^\top Z_{\rm iso})^{-1}\big)<\sigma^2\operatorname{tr}(G^{-1}).$$
-- source:
--   Balestriero and LeCun, LeJEPA: Provable and Scalable Self-Supervised Learning Without the Heuristics, arXiv:2511.08544v3 (2025), Section 3.1, Lemma 2, with the setting of the paragraph before Lemma 1 and its proof in Appendix B.2

import Mathlib
import Definitions.Def_LeJEPA_Basic

open MeasureTheory Matrix Filter Topology
open scoped ENNReal InnerProductSpace

namespace LeJEPA

theorem anisotropy_amplifies_variance {N K : ℕ} (hK : 0 < K) (Zaniso Ziso : Matrix (Fin N) (Fin K) ℝ)
    (hspan : LinearMap.range (Matrix.toLin' Zaniso) = LinearMap.range (Matrix.toLin' Ziso))
    (hpos : (Zanisoᵀ * Zaniso).PosDef)
    (hiso : Zisoᵀ * Ziso = ((Zanisoᵀ * Zaniso).trace / K) • (1 : Matrix (Fin K) (Fin K) ℝ))
    (haniso : Zanisoᵀ * Zaniso ≠ ((Zanisoᵀ * Zaniso).trace / K) • (1 : Matrix (Fin K) (Fin K) ℝ))
    (σ : ℝ) (hσ : 0 < σ) :
    olsTotalVariance Ziso σ < olsTotalVariance Zaniso σ := by sorry

end LeJEPA
