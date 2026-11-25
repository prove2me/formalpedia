-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_swept_fixed_support_of_core_resultant
-- name    : HodgeComputer.FourPlusTwoResidual.exists_swept_fixed_support_of_core_resultant
-- status  : Open
-- author  : @pageman
-- created : 2026-11-25T05:49:20.196042+00:00
-- url     : https://prove2.me/theorems/12afd3db-cb08-4543-a04b-fc24e382b40b
-- title:
--   Core swept resultant yields an affine fixed-support numerator solution
-- statement:
--   **Claim.** From any nonzero four-variable polynomial $R$ with $H\nmid R$ and $H\nmid\sigma_{AB}^*R$, there exist a nonzero affine denominator $B\in\mathbb{C}[x,y,z]$ with $h\nmid B$ (where $h=$`affineCore`) together with a pole order $n$ and numerators $N_0,N_1,N_2$ satisfying `FixedSupportEquation B n N`:
--
--   $$
--   2 B\sum_i N_i\partial_i h-3 h\Bigl(B\sum_i\partial_i N_i-n\sum_i N_i\partial_i B\Bigr)=3 y^3 B^{n+1}.
--   $$
--
--   The transport is: form $D_{\mathrm{geom}}=R\cdot\sigma_{AB}^*R$, dehomogenize / specialize to an affine support $B$, clear boundary poles by a power $n$, and solve the resulting linear numerator system for $(N_0,N_1,N_2)$ (Attack Gamma+Delta of Discussion #120).
--
--   **Formalization Note.** Conclusion strengthens `exists_fixed_support_core_solution` by the coprimality $h\nmid B$.
-- source:
--   Hodge.computer Discussion #120 (swept resultant + linear numerators); WORMHOLE φ = dehomogenize/specialize then linear solve, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoSymmetry
import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.exists_swept_fixed_support_of_core_resultant
    (hR : ∃ (R : MvPolynomial (Fin 4) ℂ),
      R ≠ 0 ∧
        ¬(HodgeComputer.FourPlusTwoResidual.core ∣ R) ∧
          ¬(HodgeComputer.FourPlusTwoResidual.core ∣
              HodgeComputer.FourPlusTwoResidual.flipAB R)) :
    ∃ (B : MvPolynomial (Fin 3) ℂ) (n : ℕ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ),
      B ≠ 0 ∧
        ¬(HodgeComputer.FourPlusTwoResidual.affineCore ∣ B) ∧
          HodgeComputer.FourPlusTwoResidual.FixedSupportEquation B n N := by sorry
