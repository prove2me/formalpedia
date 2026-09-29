-- Prove2me | Theorems.Thm_ModularCurve_reductionModL_surjective
-- name    : ModularCurve.reductionModL_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/b1b44929-aa1b-5662-8d19-6da831a3b745
-- title:
--   Reduction mod ℓ on modular divisor classes is surjective
-- statement:
--   Let $N$ be a nonzero natural number and $\ell$ a prime that does not divide $N$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which satisfies `LiesOverPrime ℓ`, that is, the image of $\ell$ in $\overline{\mathbb{Q}}$ lies in the set of nonunits of $A$ (equivalently, $\ell$ lies in the maximal ideal of the valuation ring $A$), and let $k =$ `IsLocalRing.ResidueField A` be its residue field. The assertion is that the additive homomorphism `reductionModL A N`, from `JZero N`, the degree-zero divisor class group $\mathrm{Pic}^0$ of the modular function field `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$, to `JZeroC k N`, the degree-zero divisor class group $\mathrm{Pic}^0$ of the function field `modularFunctionFieldFullC k N` over $k$, is surjective as a map of sets. Here `reductionModL A N` is `reductionAlong A (IsLocalRing.residue A) N`, which by definition is the reduction map on $\mathrm{Pic}^0$ attached to a choice of data witnessing `ReductionInputsAlong A (IsLocalRing.residue A) N`, and is the zero homomorphism should no such data exist; so the conclusion also encodes that these reduction inputs do exist under the stated hypotheses.
--
--   This is Deuring's reduction of divisor classes on the modular curve at a prime $\ell$ of good reduction, in the form: the specialisation map from the degree-zero divisor classes in characteristic zero onto those of the special fibre is onto. It is used in the comparison of Hecke and Frobenius actions on the reduction, notably in identifying the Frobenius pushforward on the special fibre with the map induced by `reductionModL`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_reductionModL_surjective.lean

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.reductionModL_surjective (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    Function.Surjective (reductionModL A N) := by sorry
