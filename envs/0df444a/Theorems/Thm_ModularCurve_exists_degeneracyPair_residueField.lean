-- Prove2me | Theorems.Thm_ModularCurve_exists_degeneracyPair_residueField
-- name    : ModularCurve.exists_degeneracyPair_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/569b6467-3d33-53a8-8c97-c67c74ce334e
-- title:
--   Two integral degeneracy embeddings of modular function fields
-- statement:
--   Let $M$ and $s$ be nonzero natural numbers, let $q'$ be a prime, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ satisfying `LiesOverPrime` for $q'$, that is, the image of $q'$ in $\overline{\mathbb{Q}}$ is a nonunit of $A$, so that $q'$ lies in the maximal ideal; assume moreover that $q' \nmid M s$. Write $\kappa$ for the residue field of $A$, which then has characteristic $q'$. For a nonzero level $N$, `modularFunctionFieldC` $\kappa\,N$ denotes the intermediate field of the Laurent series field $\kappa((q))$ generated over $\kappa$ by the two elements `jqModC` $\kappa$, equal to $q^{-1}$ times the image in $\kappa$ of the integral power series `jNum`, the $q$-expansion of $j$, and its image under the exponent-scaling ring homomorphism `qExpand` $\kappa\,N$, i.e. $j(q^N)$. The assertion is that there is a family $\varphi$ indexed by `Fin 2` of $\kappa$-algebra homomorphisms from `modularFunctionFieldC` $\kappa\,M$ to `modularFunctionFieldC` $\kappa\,(Ms)$ whose underlying ring homomorphisms are both integral, such that for every element $x$ of the level-$M$ field, $\varphi_0(x)$ equals $x$ as a Laurent series, and $\varphi_1(x)$ equals `qExpand` $\kappa\,s$ applied to $x$, the substitution $q \mapsto q^s$.
--
--   This is the existence statement for the pair of degeneracy embeddings of the modular function field of level $M$ into that of level $Ms$ over the residue characteristic $q'$ fibre, the two maps through which the Hecke correspondence of level $s$ acts; the $q$-expansion conditions pin each embedding down, since a homomorphism of these fields is determined by its values on $j(q)$ and $j(q^M)$. It is used in the construction of glued specialisations of places along the two-level degeneracy glue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_degeneracyPair_residueField.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ValuationSubring_ReduceAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.exists_degeneracyPair_residueField (M s q' : ℕ) [NeZero M] [NeZero s] (hq' : q'.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q') (hq'Ms : ¬ q' ∣ M * s) :
    haveI : NeZero q' := ⟨hq'.ne_zero⟩
    haveI : Fact q'.Prime := ⟨hq'⟩
    haveI : CharP (ResidueField A) q' := ValuationSubring.charP_residueField_of_liesOverPrime_def hq' hA
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (M * s)
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    ∃ (φ : Fin 2 → (↥(modularFunctionFieldC (ResidueField A) M) →ₐ[ResidueField A]
        ↥(modularFunctionFieldC (ResidueField A) (M * s))))
      (_ : ∀ i, (φ i).toRingHom.IsIntegral),
      (∀ x, ((φ 0 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) :
          LaurentSeries (ResidueField A)) = x) ∧
      (∀ x, ((φ 1 x : ↥(modularFunctionFieldC (ResidueField A) (M * s))) :
          LaurentSeries (ResidueField A)) = qExpand (ResidueField A) s x) := by sorry
