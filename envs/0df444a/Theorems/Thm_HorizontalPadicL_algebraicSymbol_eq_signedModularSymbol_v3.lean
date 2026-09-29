-- Prove2me | Theorems.Thm_HorizontalPadicL_algebraicSymbol_eq_signedModularSymbol_v3
-- name    : HorizontalPadicL.algebraicSymbol_eq_signedModularSymbol_v3
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T11:41:01.433143+00:00
-- url     : https://prove2.me/theorems/68a6ab8a-b6f8-48a6-9df1-0a35b4103c7f
-- title:
--   Algebraic symbols equal signed modular symbols at nonzero modulus
-- statement:
--   Let f be an eigenform of positive level and weight at least two, and let P be an MTT period system. For j at most k-2 and nonzero rational modulus m, expansion of (mX+a)^j identifies the embedded algebraic symbol, multiplied by its period, with the signed classical modular symbol. No newform hypothesis is required.
-- source:
--   Mazur--Tate--Teitelbaum modular-symbol period formalism; the analytic binomial-collapse argument formalized in the MTT distribution-relation development; Kriz--Nordentoft, https://arxiv.org/pdf/2310.20678, Section 3.

import Definitions.Def_KN_SeededThetaConstructionV2B

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- At positive level and classical weight, expanding `(mX+a)^j` identifies
`MTT.algebraicSymbol` with the signed classical modular symbol.  The modulus is
required to be nonzero, as in the modular-symbol construction. -/
theorem algebraicSymbol_eq_signedModularSymbol_v3
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ}
    (hN : 0 < N) (hk : 2 ≤ k) (f : MTT.Eigenform N k ι)
    (P : MTT.Periods k ι f.form) (s : Bool) (j : ℕ) (a m : ℚ)
    (hj : j ≤ k - 2) (hm : m ≠ 0) :
    ι (MTT.algebraicSymbol P s j a m) * P.omega s =
      signedModularSymbol f.form s j a m := by
  sorry

end HorizontalPadicL
