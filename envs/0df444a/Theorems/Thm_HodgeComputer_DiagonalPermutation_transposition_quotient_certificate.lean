-- Prove2me | Theorems.Thm_HodgeComputer_DiagonalPermutation_transposition_quotient_certificate
-- name    : HodgeComputer.DiagonalPermutation.transposition_quotient_certificate
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T04:57:49.693189+00:00
-- url     : https://prove2.me/theorems/b4cd047c-1b0d-4ece-b89e-5e42a0d6f2ad
-- title:
--   Projective Hodge certificate for the (01)-transposition-invariant source on diagonal-permutation
-- statement:
--   Let $F \in \mathbb{C}[X_0, X_1, X_2, Y_0, Y_1, Y_2]$ be the simultaneous-$S_3$-invariant sextic of `diagonal-permutation`, and let
--
--   $$
--   B_2 = X_0^3 Y_0^3 + X_1^3 Y_1^3 - 2 X_2^3 Y_2^3
--   $$
--
--   be the $(01)$-transposition-invariant degree-$6$ source `transpositionSource`. The theorem states that $B_2$ admits a rational Hodge certificate at pole order $q = 1$ on $V(F) \subset \mathbb{P}^5$:
--
--   $$
--   \operatorname{HasCertificate}(F,\; B_2,\; 6,\; 1).
--   $$
--
--   Because the diagonal $S_3$ action preserves $F$ and satisfies $A = X_0^3 Y_0^3 - X_1^3 Y_1^3 = \frac{1}{3}(\sigma_{12} B_2 - \sigma_{02} B_2)$, proving this single reflection-even certificate suffices to prove `HodgeComputer.DiagonalPermutation.certificate`.
-- source:
--   Hodge.computer GitHub Discussion #177 (`diagonal-permutation`), transposition quotient reduction of `benediamond` (2026-10-23, comment `DC_kwDOVLOOJc4BJDbi`), https://github.com/hodge-computer/sextics/discussions/177

import Definitions.Def_HodgeComputerDiagonalPermutationQuotient

theorem HodgeComputer.DiagonalPermutation.transposition_quotient_certificate :
    HodgeComputer.HasCertificate
      HodgeComputer.DiagonalPermutation.F
      HodgeComputer.DiagonalPermutation.transpositionSource 6 1 := by sorry
