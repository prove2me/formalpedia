-- Prove2me | Theorems.Thm_MTT_Cohomology_integration_cochain_injective
-- name    : MTT.Cohomology.integration_cochain_injective
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-06T16:45:36.866653+00:00
-- url     : https://prove2.me/theorems/4517a847-79d3-42b1-8f1e-a22121966e2c
-- title:
--   Injectivity of cusp-to-cusp integration
-- statement:
--   Let $N>0$ and $k\ge 2$, and let
--
--   $$
--   I:S_k(\Gamma_1(N))\longrightarrow H_c(N,k-2;\mathbf C)
--   $$
--
--   be the complex-linear map whose underlying modular symbol is cusp-to-cusp integration, normalized by $-2\pi i$. Then $I$ is injective: a cusp form whose integrals between every pair of rational cusps vanish is identically zero.
--
--   This is the analytic injectivity assertion in the modular-symbol realization of the Eichler–Shimura map.
-- source:
--   Shimura, Introduction to the Arithmetic Theory of Automorphic Functions (1971), Chapter 8; Ash–Stevens, Modular forms in characteristic l and special values of their L-functions (1986), §2, Theorem 2.3, p. 853, https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf.

import Definitions.Def_MTT_Cohomology_Integration
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.integration_cochain_injective
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, (I f).val = integrationCochain f) :
    Function.Injective I := by sorry
