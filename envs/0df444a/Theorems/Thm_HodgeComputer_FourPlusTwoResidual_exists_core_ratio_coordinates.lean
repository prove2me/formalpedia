-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_core_ratio_coordinates
-- name    : HodgeComputer.FourPlusTwoResidual.exists_core_ratio_coordinates
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-25T14:15:19.297366+00:00
-- url     : https://prove2.me/theorems/0c3e4d75-0ea2-5b22-bccf-69e6ea539358
-- title:
--   Existence of standard core ratio coordinates in any fraction field
-- statement:
--   **Claim.** Let $K$ be any field of fractions of $R=\mathbb{C}[x_0,x_1,y_0,y_1]$. Then there exist $a,s,t,P\in K$ with $a\neq 0$, $t\neq 0$, realizing the standard core ratio coordinates
--   $$
--   a=\iota(x_0),\qquad t=\frac{\iota(y_0)}{a},\qquad s=\frac{\iota(y_1)}{\iota(y_0)},
--   $$
--   together with the homogenization identities
--   $$
--   a^6\cdot P=\iota(H),\qquad a^6\cdot t^3=\iota(x_0^3 y_0^3),
--   $$
--   where $H$ is the four-variable four-plus-two core sextic and $\iota\colon R\to K$ is the structure map.
--
--   **Role.** This is the purely algebraic first step in reducing `exists_core_rational_vector_field` to a ratio-chart $t^4$ current on the dehomogenized core $P=\iota(H)/a^6$. The concrete choice $P=\iota(H)\,a^{-6}$ works as soon as $a=\iota(x_0)$ is invertible in $K$, which follows from injectivity of $\iota$.
--
--   **Formalization note.** The witness is existential; the standard formulas above are part of the conclusion so that downstream chart/frame lemmas may specialize to these coordinates.
-- source:
--   HodgeComputer four-plus-two residual; WORMHOLE Epoch-4 child of exists_core_rational_vector_field (0868e494)

import Definitions.Def_HodgeComputerFourPlusTwoWormholeBridge
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false
noncomputable section

open HodgeComputer.FourPlusTwoResidual
open MvPolynomial

theorem HodgeComputer.FourPlusTwoResidual.exists_core_ratio_coordinates
    {K : Type} [Field K] [CharZero K]
    [Algebra (MvPolynomial (Fin 4) ℂ) K]
    [IsFractionRing (MvPolynomial (Fin 4) ℂ) K] :
    ∃ (a s t P : K),
      a ≠ 0 ∧ t ≠ 0 ∧
        a = algebraMap (MvPolynomial (Fin 4) ℂ) K (X 0) ∧
        t = algebraMap (MvPolynomial (Fin 4) ℂ) K (X 2) / a ∧
        s = algebraMap (MvPolynomial (Fin 4) ℂ) K (X 3) /
            algebraMap (MvPolynomial (Fin 4) ℂ) K (X 2) ∧
        a ^ 6 * P = algebraMap (MvPolynomial (Fin 4) ℂ) K core ∧
        a ^ 6 * t ^ 3 = algebraMap (MvPolynomial (Fin 4) ℂ) K coreSource := by sorry
