-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_mapped_coeff_transport_monomial
-- name    : OAI.PiExponent.FormalInterpolation.mapped_coeff_transport_monomial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:03:35.801637+00:00
-- url     : https://prove2.me/theorems/02e3f264-c92e-44bd-bddf-51112c914e85
-- title:
--   Coefficient transport for a monomial
-- statement:
--   For a source monomial, the embedded coefficient at combined exponent `(s,b)` is its polynomial coefficient at `s` exactly when the source-variable exponent is `b`; otherwise it is zero.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem OAI.PiExponent.FormalInterpolation.mapped_coeff_transport_monomial
    {m : Nat} (d : Fin m →₀ Nat) (q : Polynomial Complex)
    (s : Nat) (b : Fin m → Nat) :
    (MvPolynomial.aeval
      (fun i : Fin m => (MvPolynomial.X (i.succ : Fin (m + 1)) :
        MvPolynomial (Fin (m + 1)) Complex))
      (MvPolynomial.map
        (show Polynomial Complex →+* MvPolynomial (Fin (m + 1)) Complex from
          (Polynomial.aeval
            (MvPolynomial.X (0 : Fin (m + 1)) :
              MvPolynomial (Fin (m + 1)) Complex)).toRingHom)
        (MvPolynomial.monomial d q))).coeff
        (InterpolationMatrix.exponentVector (Fin.cases s b)) =
    if d = InterpolationMatrix.exponentVector b then q.coeff s else 0 := by sorry
