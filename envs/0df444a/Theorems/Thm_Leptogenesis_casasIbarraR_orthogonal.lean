-- Prove2me | Theorems.Thm_Leptogenesis_casasIbarraR_orthogonal
-- name    : Leptogenesis.casasIbarraR_orthogonal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:06:36.936651+00:00
-- url     : https://prove2.me/theorems/367f5d6d-f8e0-4d09-a681-b5f4cee5d6ae
-- title:
--   The Casas–Ibarra matrix $R$ is complex orthogonal (Eq. 2.11)
-- statement:
--   Let $v>0$, $M_1,M_2,M_3>0$, $\lambda$ a complex $3\times3$ matrix, and suppose $[m]=U^*D_mU^\dagger$ with $U$ unitary and all light masses $m_i>0$. Then the Casas–Ibarra matrix $$R=D_m^{-1/2}U^T\lambda D_M^{-1/2}v_u$$ of Eq. (2.11) is a complex orthogonal matrix: $R^TR=RR^T=1$.
-- source:
--   S. Davidson, E. Nardi, Y. Nir, Leptogenesis, Physics Reports 466 (2008) 105–177, https://doi.org/10.1016/j.physrep.2008.06.002, Sec. 2.1.1, Eq. (2.11) (p. 112)

import Mathlib
import Definitions.Def_Leptogenesis_SeesawDefs

open Matrix

namespace Leptogenesis

/-- Eq. (2.11): the Casas–Ibarra matrix `R` is complex orthogonal. -/
theorem casasIbarraR_orthogonal (v : ℝ) (hv : 0 < v) (M : Fin 3 → ℝ) (hM : ∀ k, 0 < M k)
    (lam : Matrix (Fin 3) (Fin 3) ℂ) (U : Matrix (Fin 3) (Fin 3) ℂ) (masses : Fin 3 → ℝ)
    (hdiag : IsLightMassDiagonalization (lightMassMatrix v M lam) U masses)
    (hpos : ∀ i, 0 < masses i) :
    (casasIbarraR v M lam U masses)ᵀ * casasIbarraR v M lam U masses = 1 ∧
      casasIbarraR v M lam U masses * (casasIbarraR v M lam U masses)ᵀ = 1 := by sorry

end Leptogenesis
