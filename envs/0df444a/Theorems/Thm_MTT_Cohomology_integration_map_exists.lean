-- Prove2me | Theorems.Thm_MTT_Cohomology_integration_map_exists
-- name    : MTT.Cohomology.integration_map_exists
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-06T16:49:25.602717+00:00
-- url     : https://prove2.me/theorems/d4b16849-42c3-4d24-aab6-e79567b732f4
-- title:
--   Existence of the Hecke-equivariant integration map
-- statement:
--   There is a complex-linear map from weight-k cusp forms of level N to compactly supported group cohomology with degree k-2 binary polynomial coefficients, intertwining the explicitly normalized prime Hecke operators, whose coefficient evaluation on the path from infinity to a rational cusp r equals binomial(k-2,j) times the modular integral of f against X^j at r. Injectivity is deliberately not asserted: this node isolates the analytic construction of the class, namely that the path integral of f(z)(zX+Y)^(k-2) is a Gamma-equivariant cocycle on pairs of cusps.
-- source:
--   Shimura, Introduction to the arithmetic theory of automorphic functions, Ch. 8; Mazur-Tate-Teitelbaum, Invent. Math. 84 (1986), Theorem 2.3 and §4

import Definitions.Def_MTT_Cohomology
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem MTT.Cohomology.integration_map_exists
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    ∃ I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ,
      HeckeEquivariant I ∧ ∀ f, IntegralClass f (I f) := by sorry
