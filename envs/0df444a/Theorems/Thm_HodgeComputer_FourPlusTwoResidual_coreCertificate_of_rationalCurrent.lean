-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_coreCertificate_of_rationalCurrent
-- name    : HodgeComputer.FourPlusTwoResidual.coreCertificate_of_rationalCurrent
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-24T07:29:33.743557+00:00
-- url     : https://prove2.me/theorems/6c87f45c-d622-4ff4-bffd-03172198bb31
-- title:
--   A rational vector field solving v(H) - (3/2) H div(v) = x0^3 y0^3 yields a homogeneous CoreCertificate
-- statement:
--   Let $K$ be any fraction ring of $\mathbb{C}[x_0, x_1, y_0, y_1]$ equipped with $\mathbb{Z}$-derivations $\delta_0, \dots, \delta_3 : K \to K$ extending the coordinate partial derivatives $\partial_i$. If a four-component rational vector field $v \in K^4$ satisfies
--
--   $$
--   \sum_{i=0}^3 v_i\,\delta_i(H) - \frac{3}{2} H \sum_{i=0}^3 \delta_i(v_i) = x_0^3 y_0^3,
--   $$
--
--   then there exist homogeneous polynomials $T \neq 0$ and $M_0, \dots, M_3$ satisfying `CoreCertificate T M` (with no prior grading or degree bound required on a common denominator of $v$).
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual` and GitHub Discussion #120, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

theorem HodgeComputer.FourPlusTwoResidual.coreCertificate_of_rationalCurrent :
    ∀ {K : Type} [Field K] [CharZero K]
      [Algebra (MvPolynomial (Fin 4) ℂ) K]
      [IsFractionRing (MvPolynomial (Fin 4) ℂ) K]
      (δ : Fin 4 → Derivation ℤ K K),
      (∀ (i : Fin 4) (p : MvPolynomial (Fin 4) ℂ),
        δ i (algebraMap (MvPolynomial (Fin 4) ℂ) K p) =
          algebraMap (MvPolynomial (Fin 4) ℂ) K (MvPolynomial.pderiv i p)) →
      ∀ (v : Fin 4 → K),
        HodgeComputer.FourPlusTwoResidual.CoreRationalEquation δ v →
        ∃ (T : MvPolynomial (Fin 4) ℂ) (M : Fin 4 → MvPolynomial (Fin 4) ℂ),
          HodgeComputer.FourPlusTwoResidual.CoreCertificate T M := by sorry
