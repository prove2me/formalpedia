-- Prove2me | Theorems.Thm_HodgeComputer_Formal_QuadraticCovers_infinityCoefficient_mapRatFunc
-- name    : HodgeComputer.Formal.QuadraticCovers.infinityCoefficient_mapRatFunc
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:35:47.724723+00:00
-- url     : https://prove2.me/theorems/c2c81c68-e5e5-48e4-8377-216968d930d2
-- title:
--   Functoriality of the residue at infinity under field embeddings
-- statement:
--   Let $\varphi : K \to L$ be a homomorphism of fields and $f \in \operatorname{RatFunc}(K)$. Then
--
--   $$\operatorname{infinityCoefficient}\bigl(\operatorname{mapRatFunc}(\varphi)(f)\bigr) = \varphi\bigl(\operatorname{infinityCoefficient}(f)\bigr).$$
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/QuadraticCovers/RationalCoverResidues.lean#L434-L457

import Definitions.Def_HodgeComputerFormal_CoverResidues
set_option autoImplicit false

theorem HodgeComputer.Formal.QuadraticCovers.infinityCoefficient_mapRatFunc
    {K L : Type*} [Field K] [Field L] (f : K →+* L) (g : RatFunc K) :
    CrossedRationalResidue.infinityCoefficient (QuadraticCovers.mapRatFunc f g) =
      f (CrossedRationalResidue.infinityCoefficient g) := by sorry
