-- Prove2me | Theorems.Thm_HodgeComputer_PolarizedK3Remainder_normalChart_X0_pow_ten_legal
-- name    : HodgeComputer.PolarizedK3Remainder.normalChart_X0_pow_ten_legal
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-25T02:51:27.811339+00:00
-- url     : https://prove2.me/theorems/b662741c-eb38-4c24-b063-4a1dca52d08f
-- title:
--   The monomial $X_0^{10}$ is a legal degree-ten NormalChart denominator
-- statement:
--   Let $F$ be the polarized-k3-remainder sextic. Set
--   $$S=X_0^{10}\in\mathbb C[X_0,X_1,X_2,Y_0,Y_1,Y_2].$$
--   Then $S\neq0$, $S$ is homogeneous of degree exactly $10$, and $\operatorname{IsRelPrime}(F,S)$.
--
--   This isolates the structural (legality) half of the CycleQ2-style specialization of the degree-ten NormalChart residue system at the coordinate power $X_0^{10}$, parallel to `HodgeComputer.CycleQ2.normalChart_X2_cubed_denominator_legal`. Relative primality follows because every irreducible factor of $S$ is associate to $X_0$, while $X_0\nmid F$ (e.g. the monomial $Y_2^6$ appears in $F$).
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/docs/05-computation.md §5.1–5.2 (fix a denominator; legal even classes); parallel CycleQ2 X2^3 legality; data/polarized-k3-remainder/instance.rec

import Definitions.Def_HodgeComputerPolarizedK3Remainder
import Definitions.Def_HodgeComputerNormalChart
set_option autoImplicit false
open HodgeComputer HodgeComputer.PolarizedK3Remainder MvPolynomial

theorem HodgeComputer.PolarizedK3Remainder.normalChart_X0_pow_ten_legal :
    let S : AmbientPoly n := (MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (10 : ℕ)
    S ≠ 0 ∧ S.IsHomogeneous 10 ∧ IsRelPrime F S := by sorry
