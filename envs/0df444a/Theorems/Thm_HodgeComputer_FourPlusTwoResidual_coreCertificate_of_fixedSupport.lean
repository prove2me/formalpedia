-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_coreCertificate_of_fixedSupport
-- name    : HodgeComputer.FourPlusTwoResidual.coreCertificate_of_fixedSupport
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-24T07:29:33.137801+00:00
-- url     : https://prove2.me/theorems/db00795d-eeb1-4776-96f7-728fa2a444bb
-- title:
--   Fixed-denominator affine polynomial numerators on H(1,x,y,z) yield a homogeneous CoreCertificate
-- statement:
--   Let $h(x,y,z) = H(1,x,y,z) \in \mathbb{C}[x,y,z]$ be the dehomogenized four-plus-two core (`affineCore`). For any nonzero polynomial $B \in \mathbb{C}[x,y,z]$, natural number $n \in \mathbb{N}$, and polynomial triple $N = (N_0, N_1, N_2) \in \mathbb{C}[x,y,z]^3$ satisfying the linear numerator identity
--
--   $$
--   2 B \sum_{i=0}^2 N_i\,\partial_i h - 3 h \Bigl(B \sum_{i=0}^2 \partial_i N_i - n \sum_{i=0}^2 N_i\,\partial_i B\Bigr) = 3 y^3 B^{n+1},
--   $$
--
--   there exist homogeneous polynomials $T, M$ in $\mathbb{C}[x_0, x_1, y_0, y_1]$ satisfying `CoreCertificate T M`.
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual` and GitHub Discussion #120, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

theorem HodgeComputer.FourPlusTwoResidual.coreCertificate_of_fixedSupport :
    ∀ (B : MvPolynomial (Fin 3) ℂ) (n : ℕ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ),
      B ≠ 0 →
      HodgeComputer.FourPlusTwoResidual.FixedSupportEquation B n N →
      ∃ (T : MvPolynomial (Fin 4) ℂ) (M : Fin 4 → MvPolynomial (Fin 4) ℂ),
        HodgeComputer.FourPlusTwoResidual.CoreCertificate T M := by sorry
