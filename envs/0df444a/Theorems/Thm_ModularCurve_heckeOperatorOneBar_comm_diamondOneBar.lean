-- Prove2me | Theorems.Thm_ModularCurve_heckeOperatorOneBar_comm_diamondOneBar
-- name    : ModularCurve.heckeOperatorOneBar_comm_diamondOneBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/c7322c5a-28b5-50a6-9cee-67e76ff93561
-- title:
--   Hecke operators commute with diamond operators on J₁(M)
-- statement:
--   Let $M$ be a nonzero natural number, let $\ell$ be a prime and let $d$ be a natural number. The object acted on is `JOne M`, the degree-zero divisor class group $\mathrm{Pic}^0$ of the function field `x1FunctionFieldBar M` over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Here `heckeOperatorOneBar M ℓ` is the $\mathbb{Z}$-linear endomorphism of `JOne M` underlying the additive map `heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ`, which by definition is the correspondence `heckePic0OneBar` built from the two degeneracy maps `heckeAlphaOneBar` and `heckeBetaOneBar` when the predicate `HeckeInputsOneAlong (AlgebraicClosure ℚ) M ℓ` holds (this packages integrality of the two maps together with the fundamental identity, finiteness and norm-formula data the correspondence needs), and is the zero map otherwise. The endomorphism `diamondOneBar M d` is the $\mathbb{Z}$-linear map obtained from the action on `JOne M` of the semilinear automorphism `SemilinearAut.ofAlgAut (diamondAutBar M d)`, i.e. the pair consisting of the base change `diamondAutBar M d` to $\overline{\mathbb{Q}}$ of the diamond automorphism `diamondAut M d` of the function field together with the identity on $\overline{\mathbb{Q}}$. The assertion is that these two endomorphisms commute in the ring `Module.End ℤ (JOne M)`.
--
--   This is the commutation $\langle d\rangle T_\ell = T_\ell \langle d\rangle$ of the Hecke and diamond operators on the Jacobian of $X_1(M)$, covering also the case $\ell \mid M$, in the form where the Hecke operator is the zero map whenever the data defining the correspondence are unavailable. It is one part of the pairwise commutation statement [`ModularCurve.heckeDiamondCommuteBar`](thm.html#ModularCurve.heckeDiamondCommuteBar), which makes `JOne M` a module over the commutative Hecke algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeOperatorOneBar_comm_diamondOneBar.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.heckeOperatorOneBar_comm_diamondOneBar (M : ℕ) [NeZero M] (ℓ : Nat.Primes)
    (d : ℕ) :
    ModularCurve.heckeOperatorOneBar M ℓ * ModularCurve.diamondOneBar M d =
      ModularCurve.diamondOneBar M d * ModularCurve.heckeOperatorOneBar M ℓ := by sorry
