-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_projected_swept_sign_translate_denominator
-- name    : HodgeComputer.FourPlusTwoResidual.exists_projected_swept_sign_translate_denominator
-- status  : Open
-- author  : @pageman
-- created : 2026-11-25T05:49:14.852608+00:00
-- url     : https://prove2.me/theorems/44b07f38-b27d-49dc-a14e-073ed9a4cacf
-- title:
--   Nonzero projected swept-surface denominator coprime to $H$ and its $\sigma_{AB}$-translate
-- statement:
--   Let $H$ be the four-variable sextic core of `four-plus-two-residual` and let $\sigma_{AB}$ be the sign involution `flipAB` on $(x_0,x_1)$.
--
--   **Claim.** There exists a nonzero polynomial $R\in\mathbb{C}[x_0,x_1,y_0,y_1]$ such that
--
--   $$
--   H\nmid R \qquad\text{and}\qquad H\nmid \sigma_{AB}^*R.
--   $$
--
--   Geometrically $R$ is a generator (or factor) of the projected swept-surface elimination ideal of the norm-contact family in Discussion #120 (Nov 22 degree $\ge 361$ lower bound on one branch). The product $D_{\mathrm{geom}}=R\cdot\sigma_{AB}^*R$ is then a legal bipartite-compatible geometric denominator. Irreducibility of $H$ converts $H\nmid R$ into coprimality.
--
--   **Formalization Note.** Uses `core` and `flipAB` from the four-plus-two core/symmetry modules.
-- source:
--   Hodge.computer Discussion #120 (kmehltretter82 Nov 22: projected swept surface / perturbed resultant; benediamond contact family), https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoSymmetry

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.exists_projected_swept_sign_translate_denominator :
    ∃ (R : MvPolynomial (Fin 4) ℂ),
      R ≠ 0 ∧
        ¬(HodgeComputer.FourPlusTwoResidual.core ∣ R) ∧
          ¬(HodgeComputer.FourPlusTwoResidual.core ∣
              HodgeComputer.FourPlusTwoResidual.flipAB R) := by sorry
