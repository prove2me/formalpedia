-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_log_shear_pullback_coordinate
-- name    : OAI.PiExponent.FormalInterpolation.truncated_log_shear_pullback_coordinate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:41:36.700534+00:00
-- url     : https://prove2.me/theorems/06eb76d3-e706-4693-9601-81666d83aa7c
-- title:
--   The inverse truncated-log shear pulls back the jet to translation
-- statement:
--   For every center, truncation profile, and polynomial, applying the truncated polynomial jet to the polynomial evaluated at the explicit inverse shear is the same as translating the later coordinates by the center and leaving the first coordinate unchanged. This removes the substitution calculation from the target theorem, which then follows by choosing the explicit inverse-shear evaluation as its witness. The statement has no boundary restrictions: it applies also when `m = 0` or some truncation order is zero. A proof can check the images of the generators—`X 0 - 1` maps to `X 0`, and each later inverse-shear coordinate maps to `c i + X (i+1)`—then use composition of evaluation homomorphisms to extend the identities to `Q`.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.truncated_log_shear_pullback_coordinate
    {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat)
    (Q : MvPolynomial (Fin (m + 1)) Complex) :
    truncatedPolynomialJet c T
      (MvPolynomial.aeval
        (fun i : Fin (m + 1) =>
          Fin.cases (MvPolynomial.X 0 - 1)
            (fun j => MvPolynomial.X j.succ -
              Polynomial.aeval (MvPolynomial.X 0 - 1)
                (InterpolationMatrix.truncatedLog (T j))) i) Q) =
    MvPolynomial.aeval
      (fun i : Fin (m + 1) =>
        MvPolynomial.C (Fin.cases (0 : Complex) c i) + MvPolynomial.X i) Q := by sorry
