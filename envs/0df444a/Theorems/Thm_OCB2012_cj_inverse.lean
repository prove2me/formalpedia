-- Prove2me | Theorems.Thm_OCB2012_cj_inverse
-- name    : OCB2012.cj_inverse
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T09:44:33.548471+00:00
-- url     : https://prove2.me/theorems/d214695e-d95d-41bd-a076-f3a5b6cb0a03
-- title:
--   Appendix B, Eq. (15): a linear map is recovered from its CJ matrix, $\mathcal M(\rho) = (\mathrm{Tr}_{X_1}[\rho^{X_1}M^{X_1X_2}])^T$
-- statement:
--   Let $\mathcal M : \mathcal L(\mathcal H^{X_1})\to\mathcal L(\mathcal H^{X_2})$ be linear with CJ matrix $M^{X_1X_2} = [\mathcal I\otimes\mathcal M(|\phi^+\rangle\langle\phi^+|)]^T$. Then for every operator $\rho$ on $\mathcal H^{X_1}$,
--
--   $$\mathcal M(\rho) = \Big(\mathrm{Tr}_{X_1}\big[(\rho\otimes\mathbb 1^{X_2})\,M^{X_1X_2}\big]\Big)^{T}.$$
--
--   This is the inverse direction of the CJ isomorphism, Eq. (15) of Appendix B. It shows that the CJ matrix determines the map, so statements about CJ matrices are statements about operations.
-- source:
--   O. Oreshkov, F. Costa, C. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, Appendix B, Eq. (15)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Definitions.Def_OCB2012_cj

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem cj_inverse {x1 x2 : Type*} [Fintype x1] [Fintype x2] [DecidableEq x1] [DecidableEq x2]
    (Φ : Matrix x1 x1 ℂ →ₗ[ℂ] Matrix x2 x2 ℂ) (ρ : Matrix x1 x1 ℂ) :
    Φ ρ = (ptrace₁ ((ρ ⊗ₖ (1 : Matrix x2 x2 ℂ)) * cjMatrix Φ))ᵀ := by sorry

end OCB2012
