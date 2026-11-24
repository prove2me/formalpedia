-- Prove2me | Theorems.Thm_HodgeComputer_Formal_QuadraticCovers_residue_mapRatFunc
-- name    : HodgeComputer.Formal.QuadraticCovers.residue_mapRatFunc
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:34:46.559319+00:00
-- url     : https://prove2.me/theorems/19c3fc33-af98-4ef9-9315-203f2c99f21d
-- title:
--   Functoriality of residues under field embeddings
-- statement:
--   Let $\varphi : K \to L$ be a homomorphism of fields, $a \in K$, and $f \in \operatorname{RatFunc}(K)$. Then
--
--   $$\operatorname{residue}\bigl(\varphi(a),\, \operatorname{mapRatFunc}(\varphi)(f)\bigr) = \varphi\bigl(\operatorname{residue}(a, f)\bigr).$$
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/QuadraticCovers/RationalCoverResidues.lean#L420-L433

import Definitions.Def_HodgeComputerFormal_CoverResidues
set_option autoImplicit false

theorem HodgeComputer.Formal.QuadraticCovers.residue_mapRatFunc
    {K L : Type*} [Field K] [Field L] (f : K →+* L) (a : K) (g : RatFunc K) :
    CrossedRationalResidue.residue (f a) (QuadraticCovers.mapRatFunc f g) =
      f (CrossedRationalResidue.residue a g) := by sorry
