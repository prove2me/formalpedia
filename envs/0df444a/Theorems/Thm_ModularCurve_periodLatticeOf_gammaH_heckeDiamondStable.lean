-- Prove2me | Theorems.Thm_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable
-- name    : ModularCurve.periodLatticeOf_gammaH_heckeDiamondStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/6b4f58e6-5f1b-517d-8beb-383a09d205b9
-- title:
--   Hecke and diamond stability of the Γ_H(M) period lattice
-- statement:
--   Fix a nonzero natural number $M$ and a subgroup $H \le (\mathbb{Z}/M)^\times$, and let $\Gamma = \Gamma_H(M)$ be [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained by pushing forward along the inclusion of $\Gamma_0(M)$ the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ sending $\gamma$ to the reduction of its lower-right entry. Let $\Lambda =$ [`ModularCurve.periodLatticeOf`](def/ModularCurve_PeriodOf.html#L65) $\Gamma$ be the $\mathbb{Z}$-submodule of the $\mathbb{C}$-dual of the space of weight-two cusp forms $\mathrm{CuspForm}\,\Gamma\,2$ spanned by the functionals `periodOf` $\Gamma\,\gamma =$ `periodAlongOf` $\Gamma$ evaluated at the pair of points $i$ and $\gamma \cdot i$ of the upper half-plane, as $\gamma$ ranges over $\Gamma$. The assertion is the conjunction of three statements: (i) for every prime $\ell$ with $\ell \nmid M$, the dual map of the linear operator [`CuspForm.heckeTLinH 2`](def/CuspForm_HeckeOperatorFormsGammaH.html#L224) on $\mathrm{CuspForm}\,\Gamma\,2$ carries every element of $\Lambda$ into $\Lambda$; (ii) the same for the dual of [`CuspForm.heckeULinH 2 q`](def/CuspForm_HeckeOperatorFormsGammaH.html#L171) for every prime $q$ dividing $M$; (iii) the same for the dual of [`CuspForm.diamondLinH 2 d`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132) for every $d \in (\mathbb{Z}/M)^\times$. Here the three operators are defined by cases on the stability predicates `StableT`, `StableU`, `StableD`, which for weight two hold by [`CuspForm.stableT`](thm.html#CuspForm.stableT), [`CuspForm.stableU`](thm.html#CuspForm.stableU), [`CuspForm.stableD`](thm.html#CuspForm.stableD); thus $T_\ell$ is $f \mapsto \mathrm{heckeU}\,2\,\ell\,f + f\mid_2(\rho \cdot \mathrm{heckeDiagMatrix}\,\ell)$ for a suitable $\rho \in \Gamma_0(M)$ with lower-right entry $\equiv \ell$, $U_q$ is $f \mapsto \mathrm{heckeU}\,2\,q\,f$, and $\langle d\rangle$ is $f \mapsto f\mid_2 \mathrm{gammaLift}\,M\,d$.
--
--   This is the statement that the Hecke operators $T_\ell$ ($\ell \nmid M$), $U_q$ ($q \mid M$) and the diamond operators $\langle d \rangle$ act, through their duals on weight-two cusp forms, on the period lattice of $X_H(M)$ — equivalently that they preserve $H_1(X_H(M), \mathbb{Z})$ in Manin's modular-symbol description. It packages the three lattice-stability hypotheses needed downstream, and is cited by [`ModularCurve.finite_torsion_jOne`](thm.html#ModularCurve.finite_torsion_jOne) and by [`ModularCurve.linearIndependent_rationalHeckeRepOne_of_linearIndependent`](thm.html#ModularCurve.linearIndependent_rationalHeckeRepOne_of_linearIndependent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable.lean

import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.periodLatticeOf_gammaH_heckeDiamondStable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
        (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) ∧
      (∀ (q : ℕ), q.Prime → q ∣ M → ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
        (CuspForm.heckeULinH 2 q).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) ∧
      (∀ (d : (ZMod M)ˣ), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
        (CuspForm.diamondLinH 2 d).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) := by sorry
