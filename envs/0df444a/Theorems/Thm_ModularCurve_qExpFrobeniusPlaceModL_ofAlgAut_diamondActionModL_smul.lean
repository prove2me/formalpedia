-- Prove2me | Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
-- name    : ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/b5ed2b16-a245-5add-bb98-4a4372331d96
-- title:
--   Diamond automorphisms commute with Frobenius on places
-- statement:
--   Let $K$ be an algebraically closed field of characteristic a prime $p$, let $N\ge 1$ be a nonzero natural number with $p\nmid N$, let $H'\le(\mathbb Z/N)^\times$ be a subgroup and let $\gamma\in\Gamma_0(N)$. Write $\Gamma_{H'}=$ [`CohCarrier.GammaH N H'`](def/CohCarrier_Level.html#L133) for the subgroup of $\mathrm{SL}(2,\mathbb Z)$ obtained as the image, under the inclusion of $\Gamma_0(N)$, of the preimage of $H'$ under the homomorphism $\Gamma_0(N)\to(\mathbb Z/N)^\times$ sending a matrix to the class of its lower right entry, and let $F=$ `qExpFunctionFieldC K`$\Gamma_{H'}$ be the intermediate field of the Laurent series field $K(\!(q)\!)$ generated over $K$ by all quotients $\mathrm{intSeriesC}\,K\,p_f/\mathrm{intSeriesC}\,K\,p_g$ of reductions of integral $q$-expansions $p_f,p_g$ of modular forms $f,g$ of a common weight for $\Gamma_{H'}$, the denominator being nonzero. Let $w$ be a place of $F$ over $K$, i.e. a valuation subring of $F$ containing the image of $K$, different from $F$ and a principal ideal ring. Let $\delta=$ `diamondActionModL K N H'`$\gamma$ be the value at $\gamma$ of the canonical homomorphism from $\Gamma_0(N)$ to $\mathrm{Aut}_K(F)$ which is a diamond pullback in the sense of `IsDiamondPullbackModL` (namely: $\delta$ carries any element with Laurent series $\mathrm{intSeriesC}\,K\,p_{f_1}/\mathrm{intSeriesC}\,K\,p_{g_1}$, where $f_1=f\mid_k\gamma$ and $g_1=g\mid_k\gamma$, to $\mathrm{intSeriesC}\,K\,p_f/\mathrm{intSeriesC}\,K\,p_g$), taken to be the trivial homomorphism if no such pullback exists. Acting on places through the semilinear automorphism `SemilinearAut.ofAlgAut`$\delta$, the pair consisting of $\delta$ as a ring automorphism of $F$ together with the identity of $K$, the assertion is that pointwise transport by $\delta$ commutes with `qExpFrobeniusPlaceModL K`$\Gamma_{H'}$`p`, the operation of restricting a place along the $K$-algebra endomorphism of $F$ induced by $q\mapsto q^p$ on coefficientwise-Frobenius-twisted Laurent series: $\mathrm{Fr}(\delta\cdot w)=\delta\cdot \mathrm{Fr}(w)$.
--
--   This records that the diamond automorphisms of the $q$-expansion function field of $X_{H'}(N)$ in characteristic $p\nmid N$ are defined over the prime field, in the form of a commutation with the Frobenius operation on places. It is the place-level input used by the specialisation and prolongation machinery for $J_{H}$ at places of the modular function field, where diamond-twisted places must be compared with their Frobenius restrictions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_QExpFrobeniusModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
    (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (H' : Subgroup (ZMod N)ˣ) (γ : CongruenceSubgroup.Gamma0 N)
    (w : Place K ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H'))) :
    qExpFrobeniusPlaceModL K (CohCarrier.GammaH N H') p
        (SemilinearAut.ofAlgAut (diamondActionModL K N H' γ) • w) =
      SemilinearAut.ofAlgAut (diamondActionModL K N H' γ) •
        qExpFrobeniusPlaceModL K (CohCarrier.GammaH N H') p w := by sorry
