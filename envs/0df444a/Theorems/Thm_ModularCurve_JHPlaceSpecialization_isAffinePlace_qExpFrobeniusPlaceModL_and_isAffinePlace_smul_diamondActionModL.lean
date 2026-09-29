-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
-- name    : ModularCurve.JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/dfe52a47-d30a-5189-8c98-45d3dc42914e
-- title:
--   Affine places are stable under q-Frobenius and diamonds
-- statement:
--   Fix a prime $p$ and a natural number $M\neq 0$ with $p \mid M$ and $M/p \neq 0$, and a subgroup $H \le (\mathbb{Z}/M)^{\times}$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ lying in its set of nonunits (the predicate `LiesOverPrime`), and write $\kappa$ for its residue field, assumed to be algebraically closed of characteristic $p$. Let $\bar F$ denote the field $\mathtt{qExpFunctionFieldC}\,\kappa\,(\Gamma_N)$ attached to the group $\Gamma_N =$ `JHNeronObjectAtP.ΓN p M H hpM`, and call a place $v$ of $\bar F$ over $\kappa$ *affine* when there are $x \in \bar F$ whose Laurent series is the reduced $q$-expansion $\mathtt{jqModC}\,\kappa$ of the modular invariant and $a \in \kappa$ with $v.\mathrm{HasValue}\,x\,a$, i.e. $x$ lies in the valuation subring of $v$ and its residue is the image of $a$. The conclusion is a conjunction: first, every affine place $v$ has affine image under $\mathtt{qExpFrobeniusPlaceModL}\,\kappa\,\Gamma_N\,p$, the restriction of $v$ along the integral $\kappa$-algebra map $\mathtt{qExpFrobeniusModL}$ given by $q \mapsto q^{p}$; second, for every $d \in \Gamma_0(M/p)$ and every affine $v$, the place obtained by acting on $v$ through the semilinear automorphism $\mathtt{SemilinearAut.ofAlgAut}$ of the $\kappa$-algebra automorphism $\mathtt{diamondActionModL}\,\kappa\,(M/p)\,(\mathtt{infSubgroup}\,p\,M\,H\,hpM)\,d$ (the chosen diamond-pullback homomorphism if one exists, and the trivial homomorphism otherwise, at the level group attached to the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$) is again affine.
--
--   This is the stability of the locus of affine (non-cuspidal) places of the mod-$p$ fibre function field under the $q$-power Frobenius on places and under the reduced diamond operators. It is a bookkeeping input to the regularity statements of the place-specialisation package for $J_H$ at $p$, and is cited by the prolongation-datum and model lemmas there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] :
    (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      JHPlaceSpecialization.IsAffinePlace p M H hpM A v →
      JHPlaceSpecialization.IsAffinePlace p M H hpM A (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v)) ∧
    (∀ (d : CongruenceSubgroup.Gamma0 (M / p)) (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),
      JHPlaceSpecialization.IsAffinePlace p M H hpM A v →
      JHPlaceSpecialization.IsAffinePlace p M H hpM A
        (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) d) • v)) := by sorry
