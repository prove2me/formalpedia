-- Prove2me | Theorems.Thm_MTT_Cohomology_integration_cochain_integral_class
-- name    : MTT.Cohomology.integration_cochain_integral_class
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-06T16:45:40.590224+00:00
-- url     : https://prove2.me/theorems/42f3e2ca-8754-4fed-b68b-1fb792825242
-- title:
--   Coefficient formula for the integration class
-- statement:
--   Let $N>0$ and $k\ge 2$. For the cusp-to-cusp integration class $I(f)$, evaluation on the divisor $[\infty]-[r]$ recovers the normalized vertical modular integrals. For every rational cusp $r$ and every $0\le j\le k-2$,
--
--   $$
--   \operatorname{ev}_{j,r}(I(f))=\binom{k-2}{j}\,2\pi\int_0^\infty f(r+it)(r+it)^j\,dt.
--   $$
--
--   Thus the cohomology class attached to $f$ satisfies the predicate `IntegralClass f` with the prescribed binomial coefficient and $-2\pi i$ integration normalization.
-- source:
--   Ash–Stevens, Modular forms in characteristic l and special values of their L-functions (1986), §4, pp. 863–864, https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf.

import Definitions.Def_MTT_Cohomology_Integration
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.integration_cochain_integral_class
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, (I f).val = integrationCochain f) :
    ∀ f, IntegralClass f (I f) := by sorry
