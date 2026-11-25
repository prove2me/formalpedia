-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_core_rational_current
-- name    : HodgeComputer.FourPlusTwoResidual.exists_core_rational_current
-- status  : Open
-- author  : @pageman
-- created : 2026-11-25T05:15:08.052981+00:00
-- url     : https://prove2.me/theorems/c9b6ee96-a35f-559e-b1f0-9a601151422f
-- title:
--   Existence of a four-variable rational current with source $x_0^3 y_0^3$
-- statement:
--   Let $H\in\mathbb{C}[x_0,x_1,y_0,y_1]$ be the four-variable sextic core of the Atlas instance `four-plus-two-residual`, and write $A=x_0^3 y_0^3$.
--
--   **Claim.** There exist a fraction field $K$ of $\mathbb{C}[x_0,x_1,y_0,y_1]$, coordinate derivations $\delta_0,\dots,\delta_3:K\to K$ extending the partials $\partial_i$, and a rational vector field $v\in K^4$ satisfying the twisted core equation
--
--   $$
--   \sum_{i=0}^3 v_i\,\delta_i(H)-\frac32 H\sum_{i=0}^3\delta_i(v_i)=A.
--   $$
--
--   In the platform language this is `CoreRationalEquation δ v`.
--
--   This is the geometric witness isolated by the suspension/core reduction and the contact-family construction in Discussion #120: once such a rational current exists, the proved clearing theorem `coreCertificate_of_rationalCurrent` produces a homogeneous `CoreCertificate`, and `coreCertificate_iff_bipartite` upgrades it to a `BipartiteCoreCertificate`. The expected construction is the push–pull normalization $R=K^{-1}\alpha_A$ of the norm-contact correspondence (with Gauss–Manin/Hermite–Padé horizontal correction and swept-resultant denominator extraction as computational routes).
--
--   **Formalization Note.** Uses `Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent`.
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual`; GitHub Discussion #120 (benediamond Nov 6 contact family / K=Z_*Z^* normalization; DiamondJM Nov 9 suspension bridge; kmehltretter82 Nov 21–22 rational-current finish line), https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Derivation.Basic

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.exists_core_rational_current :
    ∃ (K : Type) (_ : Field K) (_ : CharZero K)
      (_ : Algebra (MvPolynomial (Fin 4) ℂ) K)
      (_ : IsFractionRing (MvPolynomial (Fin 4) ℂ) K)
      (δ : Fin 4 → Derivation ℤ K K) (v : Fin 4 → K),
      (∀ (i : Fin 4) (p : MvPolynomial (Fin 4) ℂ),
          δ i (algebraMap (MvPolynomial (Fin 4) ℂ) K p) =
            algebraMap (MvPolynomial (Fin 4) ℂ) K (MvPolynomial.pderiv i p)) ∧
        HodgeComputer.FourPlusTwoResidual.CoreRationalEquation δ v := by sorry
