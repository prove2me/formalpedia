-- Prove2me | Theorems.Thm_HodgeComputer_Formal_RationalResidues_residue_sum_eq_infinity
-- name    : HodgeComputer.Formal.RationalResidues.residue_sum_eq_infinity
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:24:35.25533+00:00
-- url     : https://prove2.me/theorems/f2c80b8b-3c19-420e-acf7-dbca8bec1573
-- title:
--   Global residue theorem for split rational functions
-- statement:
--   Let $K$ be a field and $f \in \operatorname{RatFunc}(K)$ a rational function whose denominator splits into linear factors over $K$. Let $s \subset K$ be a finite set containing all finite poles of $f$, in the sense that $\operatorname{residue}(a, f) = 0$ for every $a \notin s$. Then
--
--   $$\sum_{a \in s} \operatorname{residue}(a, f) = \operatorname{infinityCoefficient}(f).$$
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/RationalResidues.lean#L447-L583

import Definitions.Def_HodgeComputerFormal_RationalResidues
set_option autoImplicit false
open scoped BigOperators

theorem HodgeComputer.Formal.RationalResidues.residue_sum_eq_infinity
    {K : Type*} [Field K] (f : RatFunc K) (hsplit : f.denom.Splits) (s : Finset K)
    (houtside : ∀ a, a ∉ s → CrossedRationalResidue.residue a f = 0) :
    ∑ a ∈ s, CrossedRationalResidue.residue a f =
      CrossedRationalResidue.infinityCoefficient f := by sorry
