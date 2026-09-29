-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_natCard_ssPlacesQExp_eq_toricRank_add_one_of_charP
-- name    : ModularCurve.JHNeronObjectAtP.natCard_ssPlacesQExp_eq_toricRank_add_one_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/94dd6cc1-5988-5891-a9f3-39b8809a9bb7
-- title:
--   Supersingular places of the level M/p q-expansion field count toricRank+1
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ and $M/p$ nonzero, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ belongs to `A.nonunits`, whose residue field is algebraically closed of characteristic $p$. Given level data $\Lambda$ of type `JHNeronObjectAtP.LevelData p M H hpM A` and a Néron object $O$ of type `JHNeronObjectAtP p M H hpM A hA \Lambda` (a relative group scheme over the base at $p$, with its smoothness, separatedness, finite type, surjectivity and fibre-connectedness properties, its identification of $J_H(M)$ with the generic-fibre points, its Galois and Hecke compatibilities, and its numerical field `toricRank`), the assertion is: for every algebraically closed field $K$ of characteristic $p$, the set [`ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p`](def/ModularCurve_XHDifferentialsModL.html#L27) — the places $v$ of the $q$-expansion function field over $K$ for the congruence subgroup $\Gamma_{H'}(M/p) \le \mathrm{SL}(2,\mathbb{Z})$, where $H'$ is the image of $H$ in $(\mathbb{Z}/(M/p))^\times$ and $\Gamma_{H'}(M/p)$ is the preimage of $H'$ in $\Gamma_0(M/p)$, which satisfy the predicate `IsSSPlaceQExp` — is finite of cardinality exactly $O.\mathrm{toricRank} + 1$. Here a place is a proper valuation subring of the function field containing the image of $K$ and whose valuation ring is a principal ideal ring.
--
--   This is the count of supersingular points in the special fibre at $p$ of the modular curve of level $M/p$, expressed as one more than the toric rank of the Néron object of $J_H(M)$ at $p$; equivalently, the toric rank of the special fibre equals $\#SS - 1$. It is used in the computation of the torsion of the Néron object, [`ModularCurve.natCard_torsion_eq_pow_height_add_toricRank_of_abelJacobiPin_tauFree`](thm.html#ModularCurve.natCard_torsion_eq_pow_height_add_toricRank_of_abelJacobiPin_tauFree), where it supplies the supersingular-place count independently of the chosen algebraically closed field of characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_natCard_ssPlacesQExp_eq_toricRank_add_one_of_charP.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ModularCurve.JHNeronObjectAtP.natCard_ssPlacesQExp_eq_toricRank_add_one_of_charP
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] :
    Nat.card ↥(ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) = O.toricRank + 1 := by sorry
