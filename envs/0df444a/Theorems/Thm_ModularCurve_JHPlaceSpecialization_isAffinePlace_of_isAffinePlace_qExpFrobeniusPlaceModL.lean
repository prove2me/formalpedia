-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_isAffinePlace_of_isAffinePlace_qExpFrobeniusPlaceModL
-- name    : ModularCurve.JHPlaceSpecialization.isAffinePlace_of_isAffinePlace_qExpFrobeniusPlaceModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/baa2a127-a6d6-5644-9833-c580d38c7815
-- title:
--   Affine places descend along the Frobenius on places
-- statement:
--   Let $p$ be a prime and $M$ a non-zero natural number with $p \mid M$ and $M/p$ non-zero, let $H$ be a subgroup of $(\mathbf{Z}/M)^{\times}$, and let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa = \kappa_A$ has characteristic $p$ and is algebraically closed. Write $\bar F$ for `JHNeronObjectAtP.Fbar p M H hpM` $\kappa$, the $q$-expansion function field $\kappa$-algebra attached to the group $\Gamma' =$ `JHNeronObjectAtP.ΓN p M H hpM`. The assertion is: for every place $v$ of $\bar F$ over $\kappa$ (a proper valuation subring of $\bar F$ containing $\kappa$ and a principal ideal ring), if `qExpFrobeniusPlaceModL` $\kappa\,\Gamma'\,p\,v$ — the restriction of $v$ along the integral $\kappa$-algebra map `qExpFrobeniusModL`, i.e. the $p$-power $q$-expansion operation — is an affine place, then $v$ is an affine place. Here a place $w$ is affine when there are $x \in \bar F$ whose $q$-expansion in the Laurent series over $\kappa$ is `jqModC` $\kappa$ and $a \in \kappa$ with $x$ in the valuation subring of $w$ and residue of $x$ equal to the image of $a$.
--
--   This is the converse of the affine-stability clause for the Frobenius action on places of the characteristic-$p$ fibre field: together they say that this Frobenius permutes the non-affine places, i.e. the cusps. It is used in the construction and analysis of prolongation data for the place-specialisation kit, and in the identification of the two sides (the $\infty$-side and the $0$-side) of the reduction of the modular curve at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_isAffinePlace_of_isAffinePlace_qExpFrobeniusPlaceModL.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.isAffinePlace_of_isAffinePlace_qExpFrobeniusPlaceModL
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] :
    ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      JHPlaceSpecialization.IsAffinePlace p M H hpM A (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v) →
      JHPlaceSpecialization.IsAffinePlace p M H hpM A v := by sorry
