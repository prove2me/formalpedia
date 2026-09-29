-- Prove2me | Theorems.Thm_ModularCurve_diamondDiffModLH_mem_ssPolarDifferentials_and_residue_eq_residue_inv_smul
-- name    : ModularCurve.diamondDiffModLH_mem_ssPolarDifferentials_and_residue_eq_residue_inv_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/267ab55d-a69a-50cb-9e2c-67a2cf09448d
-- title:
--   Diamond pullback preserves supersingular-polar differentials and permutes residues
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $p$ for a prime $p$, let $N \geq 1$ with $p \nmid N$, and let $H' \le (\mathbb{Z}/N)^\times$ be a subgroup; write $F =$ [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')`](def/ModularCurve_X1.html#L101), the intermediate field of $K((q))$ generated over $K$ by the integral form ratios for the congruence subgroup $\Gamma_{H'}(N)$, and let $S =$ [`ModularCurve.ssPlacesQExp K (CohCarrier.GammaH N H') p`](def/ModularCurve_XHDifferentialsModL.html#L27) be its set of supersingular places. The module $V =$ [`ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p`](def/ModularCurve_XHDifferentialsModL.html#L35) is the $K$-submodule of $\Omega[F/K]$ of differentials that are regular at every place not in $S$ and have at most a simple pole at every place of $S$. Assume given a $K$-linear map $\mathrm{res} : V \to (\mathrm{Place}\,K\,F \to K)$ such that for $\omega \in V$ and $v \in S$ the scalar $\mathrm{res}(\omega)(v)$ is a simple residue of $\omega$ at $v$ (in the sense of `HasSimpleResidue`: $\omega = f \cdot d\mathrm{Coord}_v$ with $t_v f$ having value $\mathrm{res}(\omega)(v)$), and such that $\mathrm{res}(\omega)(v) = 0$ for $v \notin S$. Fix $d \in (\mathbb{Z}/N)^\times$ and let $\sigma$ be the $K$-algebra automorphism [`ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d⁻¹)`](def/ModularCurve_XHDifferentialsModL.html#L203) of $F$, so that [`ModularCurve.diamondDiffModLH K N H' d`](def/ModularCurve_XHDifferentialsModL.html#L231) is pullback of differentials along $\sigma$. Then: (1) this pullback maps $V$ into $V$; and (2) whenever $\omega, \omega' \in V$ satisfy $\omega' =$ pullback of $\omega$, one has $\mathrm{res}(\omega')(v) = \mathrm{res}(\omega)(g^{-1} \cdot v)$ for every place $v$ of $F$ over $K$, where $g$ is the semilinear automorphism `SemilinearAut.ofAlgAut` $\sigma$ acting on places.
--
--   This is the statement that the diamond operator $\langle d\rangle$ acts on the differentials with at worst simple poles along the supersingular locus of $X_{H'}(N)$ in characteristic $p$, and that on residue vectors it acts by the induced permutation of the supersingular places. It is used in the counting arguments at the ordinary corner, where residue vectors at supersingular points carry the relevant Hecke and diamond action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diamondDiffModLH_mem_ssPolarDifferentials_and_residue_eq_residue_inv_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open AlgebraicCurve

theorem ModularCurve.diamondDiffModLH_mem_ssPolarDifferentials_and_residue_eq_residue_inv_smul
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (H' : Subgroup (ZMod N)ˣ)

    (res : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p) →ₗ[K]
      (AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) → K))
    (hres : ∀ (ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p))
      (v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))),
      v ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH N H') p →
        v.HasSimpleResidue (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) (res ω v))
    (hres0 : ∀ (ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p))
      (v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))),
      v ∉ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH N H') p → res ω v = 0)
    (d : (ZMod N)ˣ) :
    (∀ ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p),
        ModularCurve.diamondDiffModLH K N H' d (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) ∈
          ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p) ∧
    (∀ (ω ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p)),
        (ω' : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) =
          ModularCurve.diamondDiffModLH K N H' d (ω : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) →
        ∀ v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')),
          res ω' v = res ω
            ((AlgebraicCurve.SemilinearAut.ofAlgAut
                (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d⁻¹)))⁻¹ • v)) := by sorry
