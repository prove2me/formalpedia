-- Prove2me | Theorems.Thm_MTT_Cohomology_integration_linear_map_exists
-- name    : MTT.Cohomology.integration_linear_map_exists
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-06T16:45:44.928069+00:00
-- url     : https://prove2.me/theorems/f7ad6366-1756-4782-823a-612563ccc48c
-- title:
--   The integration cochain defines a linear cohomology map
-- statement:
--   Let $N>0$ and $k\ge 2$. For a weight-$k$ cusp form $f$ on $\Gamma_1(N)$, let $\Phi_f$ be the polynomial-valued cusp-to-cusp integration cochain
--
--   $$
--   \Phi_f(x,y)=-2\pi i\int_y^x f(z)(zX+Y)^{k-2}\,dz.
--   $$
--
--   Then $\Phi_f$ is homogeneous of degree $k-2$, satisfies the modular-symbol cocycle relation, and is $\Gamma_1(N)$-equivariant. Moreover, the assignment $f\mapsto\Phi_f$ defines a complex-linear map from cusp forms to $H_c(N,k-2;\mathbf C)$.
--
--   **Formalization Note** The asserted map is required to have underlying function exactly `integrationCochain f`, so the theorem includes both well-definedness in the compactly supported cohomology model and linearity.
-- source:
--   Shimura, Introduction to the Arithmetic Theory of Automorphic Functions (1971), Chapter 8; Ash–Stevens, Modular forms in characteristic l and special values of their L-functions (1986), §2, Theorem 2.3, p. 853, https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf.

import Definitions.Def_MTT_Cohomology_Integration
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.integration_linear_map_exists
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    ∃ I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ,
      ∀ f, (I f).val = integrationCochain f := by sorry
