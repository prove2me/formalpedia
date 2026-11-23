-- Prove2me | Theorems.Thm_LeJEPA_anisotropy_amplifies_bias
-- name    : LeJEPA.anisotropy_amplifies_bias
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:00:27.874596+00:00
-- url     : https://prove2.me/theorems/468cf432-a9ca-4297-b589-4805e11d043b
-- title:
--   Lemma 1: anisotropy amplifies the bias of the ridge probe
-- statement:
--   Let $Z_{\rm aniso},Z_{\rm iso}\in\mathbb{R}^{N\times K}$ ($K\ge1$) be two embedding matrices with the same column span. Let $G=Z_{\rm aniso}^\top Z_{\rm aniso}$ not be a multiple of the identity, so its eigenvalues are not all equal, and let $Z_{\rm iso}^\top Z_{\rm iso}=\bar\lambda I_K$ with $\bar\lambda=\operatorname{tr}G/K$, so that both have the same energy. Then for every ridge strength $\lambda>0$ there is a target $\beta\in\mathbb{R}^K$ (a downstream task $y=Z\beta+\varepsilon$) for which the ridge probe trained on $Z_{\rm aniso}$ has strictly larger bias:
--
--   $$\big\|(Z_{\rm iso}^\top Z_{\rm iso}+\lambda I)^{-1}Z_{\rm iso}^\top Z_{\rm iso}\beta-\beta\big\|<\big\|(G+\lambda I)^{-1}G\beta-\beta\big\|.$$
--
--   **Formalization Note** The paper's "covariance eigenvalues" are those of the Gram matrix $Z^\top Z$, which is the matrix its proof works with. The norm is the Euclidean norm.
-- source:
--   Balestriero and LeCun, LeJEPA: Provable and Scalable Self-Supervised Learning Without the Heuristics, arXiv:2511.08544v3 (2025), Section 3.1, Lemma 1, with the setting of the preceding paragraph and its proof in Appendix B.1

import Mathlib
import Definitions.Def_LeJEPA_Basic

open MeasureTheory Matrix Filter Topology
open scoped ENNReal InnerProductSpace

namespace LeJEPA

theorem anisotropy_amplifies_bias {N K : ℕ} (hK : 0 < K) (Zaniso Ziso : Matrix (Fin N) (Fin K) ℝ)
    (hspan : LinearMap.range (Matrix.toLin' Zaniso) = LinearMap.range (Matrix.toLin' Ziso))
    (hiso : Zisoᵀ * Ziso = ((Zanisoᵀ * Zaniso).trace / K) • (1 : Matrix (Fin K) (Fin K) ℝ))
    (haniso : Zanisoᵀ * Zaniso ≠ ((Zanisoᵀ * Zaniso).trace / K) • (1 : Matrix (Fin K) (Fin K) ℝ))
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ β : Fin K → ℝ, ‖WithLp.toLp 2 (ridgeBias Ziso lam β)‖ < ‖WithLp.toLp 2 (ridgeBias Zaniso lam β)‖ := by sorry

end LeJEPA
