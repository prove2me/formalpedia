-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_ringHom_ringHom_placeMap_ord_eq_qExpFunctionFieldC_of_isAlgClosed
-- name    : ModularCurve.JHNeronObjectAtP.exists_ringHom_ringHom_placeMap_ord_eq_qExpFunctionFieldC_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/4a3efd9c-7af4-508b-940b-f4581e620dd4
-- title:
--   Constant-field extension of q-expansion function fields to K
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a valuation subring $Pl$ of $\overline{\mathbb{Q}}$ whose residue field $\kappa =$ `IsLocalRing.ResidueField Pl` has characteristic $p$ and is algebraically closed; let $K$ be any algebraically closed field of characteristic $p$. The assertion is the existence of three data: a ring homomorphism $\iota : \kappa \to K$; a ring homomorphism $e_K$ from [`ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ`](def/ModularCurve_JHNeronObjectAtP.html#L29), that is from the intermediate field [`ModularCurve.qExpFunctionFieldC κ (ΓN p M H hpM)`](def/ModularCurve_X1.html#L101) of `LaurentSeries κ` obtained by adjoining to $\kappa$ the ratios `intFormRatiosC` at the level subgroup `ΓN p M H hpM`, to [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))`](def/ModularCurve_X1.html#L101), the corresponding subfield of `LaurentSeries K` for the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ cut out by the image of $H$ under the units map $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$; and a map $pl_K$ from places of the first function field over $\kappa$ to places of the second over $K$, where a place is a proper valuation subring containing the constants and whose ring is a principal ideal ring. These satisfy: for every $g$ in the source field, the Laurent series underlying $e_K g$ is the coefficientwise image [`ModularCurve.coeffMap ι`](def/ModularCurve_LaurentCoeff.html#L16) of the Laurent series $g$; and for every such $g$ and every place $v$ of the source field, $\mathrm{ord}_{pl_K(v)}(e_K g) = \mathrm{ord}_v(g)$, the order being minus the logarithm of the adic valuation attached to the place.
--
--   This is the constant-field extension of a function field with algebraically closed field of constants, in the existential form used for the special fibre at $p$: the $q$-expansion function field of the relevant level over the residue field $\kappa$ is embedded coefficientwise into the one over $K$, with places lifting and orders preserved. It feeds the corner-counting comparisons for regular differentials and residues on the modular curve, where a count made over $\kappa$ must be transported to an arbitrary algebraically closed base field of characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_ringHom_ringHom_placeMap_ord_eq_qExpFunctionFieldC_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JHNeronObjectAtP.exists_ringHom_ringHom_placeMap_ord_eq_qExpFunctionFieldC_of_isAlgClosed
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] :
    ∃ (ι : IsLocalRing.ResidueField ↥Pl →+* K)
      (eK : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl) →+* ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
      (plK : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) → AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))),
      (∀ g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl), ((eK g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap ι (g : LaurentSeries (IsLocalRing.ResidueField ↥Pl))) ∧
      (∀ (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) (v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))), (plK v).ord (eK g) = v.ord g) := by sorry
