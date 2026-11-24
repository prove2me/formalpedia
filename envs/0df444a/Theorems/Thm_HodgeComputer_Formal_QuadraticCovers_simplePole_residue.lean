-- Prove2me | Theorems.Thm_HodgeComputer_Formal_QuadraticCovers_simplePole_residue
-- name    : HodgeComputer.Formal.QuadraticCovers.simplePole_residue
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:33:27.467281+00:00
-- url     : https://prove2.me/theorems/453721c7-48d0-4be3-8806-8b6365394d00
-- title:
--   Simple-pole residue formula $P(a) / Q'(a)$
-- statement:
--   Let $K$ be a field, $P, Q \in K[X]$, and $a \in K$ a simple root of $Q$ (i.e., $Q(a) = 0$ and $Q'(a) \neq 0$). Then in $\operatorname{RatFunc}(K)$,
--
--   $$\operatorname{residue}\!\left(a,\, \frac{P}{Q}\right) = \frac{P(a)}{Q'(a)}.$$
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/QuadraticCovers/RationalCoverResidues.lean#L351-L372

import Definitions.Def_HodgeComputerFormal_RationalResidues
set_option autoImplicit false
open scoped Polynomial

theorem HodgeComputer.Formal.QuadraticCovers.simplePole_residue
    {K : Type*} [Field K] (P Q : K[X]) (a : K)
    (hQ0 : Q.eval a = 0) (hQd : Q.derivative.eval a ≠ 0) :
    CrossedRationalResidue.residue a
      (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q) =
    P.eval a / Q.derivative.eval a := by sorry
