-- Prove2me | Theorems.Thm_MTT_Cohomology_integration_cochain_hecke_equivariant
-- name    : MTT.Cohomology.integration_cochain_hecke_equivariant
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-06T16:45:35.928561+00:00
-- url     : https://prove2.me/theorems/60992b0d-f0d1-40f8-8df3-157cbfcc3d7a
-- title:
--   Hecke equivariance of cusp-to-cusp integration
-- statement:
--   Let $N>0$ and $k\ge 2$. The cusp-to-cusp integration map
--
--   $$
--   I:S_k(\Gamma_1(N))\longrightarrow H_c(N,k-2;\mathbf C)
--   $$
--
--   intertwines the analytic and modular-symbol prime Hecke operators. Explicitly, for every Dirichlet character $e$ modulo $N$, every prime $\ell$ (including primes dividing $N$), and every cusp form $f$, integrating the analytic transform $T_{\ell,e}f$ gives the modular-symbol transform $T_{\ell,e}I(f)$, with the normalizations fixed in the cohomology definitions.
-- source:
--   Ash–Stevens, Modular forms in characteristic l and special values of their L-functions (1986), §2, Theorem 2.3, p. 853, https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf; the target retains the full prime-Hecke normalization, including primes dividing N.

import Definitions.Def_MTT_Cohomology_Integration
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.integration_cochain_hecke_equivariant
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, (I f).val = integrationCochain f) :
    HeckeEquivariant I := by sorry
