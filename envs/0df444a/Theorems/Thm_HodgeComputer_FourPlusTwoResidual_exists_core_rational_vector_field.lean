-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_core_rational_vector_field
-- name    : HodgeComputer.FourPlusTwoResidual.exists_core_rational_vector_field
-- status  : Open
-- author  : @pageman
-- created : 2026-11-25T13:38:38.0328+00:00
-- url     : https://prove2.me/theorems/0868e494-8972-5bff-bf54-5322d1ace86a
-- title:
--   Existence of a rational vector field solving `CoreRationalEquation`
-- statement:
--   **Claim.** Let $K$ be any field of fractions of $R=\mathbb{C}[x_0,x_1,y_0,y_1]$, and let $\delta_i\colon K\to K$ be derivations extending the coordinate partials $\partial_i$ on $R$. Then there exists a rational vector field $v\colon\mathrm{Fin}\,4\to K$ satisfying `CoreRationalEquation`:
--
--   $$
--   \sum_i v_i\,\delta_i(\iota(H)) - \tfrac32\,\iota(H)\,\sum_i \delta_i(v_i) = \iota(x_0^3 y_0^3),
--   $$
--
--   where $H$ is the four-variable four-plus-two core sextic and $\iota\colon R\to K$ is the structure map.
--
--   This is the analytic content of constructing a four-variable rational current on the core; the Kähler lift of $\partial_i$ to $K$ is assumed as input. One route is ratio-chart transport from a $t^4$ current on the dehomogenized core $P=\iota(H)/a^6$ with ratio coordinates $a=\iota(x_0)$, $t=\iota(y_0)/a$, $s=\iota(y_1)/\iota(y_0)$; another is to clear a `FixedSupportEquation` solution into $K$.
-- source:
--   WORMHOLE child of HodgeComputer.FourPlusTwoResidual.core_rational_of_homogenized_chart_source_a6t3; https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.exists_core_rational_vector_field
    {K : Type} [Field K] [CharZero K]
    [Algebra (MvPolynomial (Fin 4) ℂ) K]
    [IsFractionRing (MvPolynomial (Fin 4) ℂ) K]
    (δ : Fin 4 → Derivation ℤ K K)
    (hδ : ∀ (i : Fin 4) (p : MvPolynomial (Fin 4) ℂ),
      δ i (algebraMap (MvPolynomial (Fin 4) ℂ) K p) =
        algebraMap (MvPolynomial (Fin 4) ℂ) K (MvPolynomial.pderiv i p)) :
    ∃ v : Fin 4 → K, HodgeComputer.FourPlusTwoResidual.CoreRationalEquation δ v := by sorry
