-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_genOpH_U_add_ofAlgAut_smul_eq_pull_degPts_of_coe_eq_qExpand
-- name    : ModularCurve.JHNeronObjectAtP.genOpH_U_add_ofAlgAut_smul_eq_pull_degPts_of_coe_eq_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/1a3c3f6d-9b68-5ba9-8306-1723cde788e0
-- title:
--   Uₚ + wₚ^* equals β^*α_* on J_H(M)
-- statement:
--   Fix a prime $p$ and a level $M \neq 0$ with $p \mid M$, $p^2 \nmid M$ and $M/p \neq 0$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, so that $H$ is the full preimage of its image `infSubgroup p M H hpM`, the image of $H$ under `ZMod.unitsMap`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ and with algebraically closed residue field of characteristic $p$, let $\Lambda$ be level data at $p$ and $O$ a Néron object `JHNeronObjectAtP p M H hpM A hA Λ`, let $S \subseteq \mathbb{N}$, and assume the function field $F = \overline{\mathbb{Q}}F(\Gamma_H(M))$, i.e. `xHFunctionFieldBar M H`, has principal divisors. Write $F' =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`. The data are: integral $\overline{\mathbb{Q}}$-algebra maps $\alpha_H, \beta_H : F' \to F$ such that $\alpha_H u$ has the same Laurent series as $u$, while $\beta_H u$ has Laurent series `qExpand` of $u$ at $p$ (substitution $q \mapsto q^p$ on exponents); a pair $\alpha\mathrm{pull} : \mathrm{Fin}\,2 \to (J_H(M/p) \to_+ J_H(M))$ of additive maps between the groups of degree-zero divisor classes; the hypothesis that `O.degPts 0` sends the class of a degree-zero divisor $D_v$ on $F$ to the class of any degree-zero divisor $D_w$ on $F'$ equal to the push-forward of $D_v$ along $\alpha_H$; the hypothesis that $\alpha\mathrm{pull}\,1$ sends the class of $D_w$ to the class of any degree-zero $D_v$ equal to the pull-back of $D_w$ along $\beta_H$; and a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F$ such that whenever $f \in F$ has the Laurent series of some $u \in F'$, the Laurent series of $\theta f$ is that of $u$ with $q$ replaced by $q^p$. The conclusion is that for every $x \in J_H(M)$,
--   $$\mathrm{genOpH}_{M,H,S}(U_p)\,x + (\theta, 1) \cdot x = \alpha\mathrm{pull}\,1\,(O.\mathrm{degPts}\,0\,x),$$
--   where the first term is `heckeOperatorHAlong` over $\overline{\mathbb{Q}}$ at $p$ and the second is the action of the semilinear automorphism `SemilinearAut.ofAlgAut θ`, acting as $\theta$ on $F$ and trivially on $\overline{\mathbb{Q}}$.
--
--   This is the identity $U_p + w_p^* = \beta_H^* \circ \alpha_{H*}$ on the Jacobian $J_H(M)$ for $p$ exactly dividing $M$, with the Atkin–Lehner involution presented through the single $q$-expansion pin on $\theta$ and with the degeneracy maps presented through the Néron-object components `O.degPts 0` and $\alpha\mathrm{pull}\,1$; unlike the roof version it cites, no roof field or fundamental-identity data appear among its hypotheses. It feeds the analysis of the action of inertia and Frobenius at $p$ on the Tate module of $J_H$, and thence the level-lowering step at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_genOpH_U_add_ofAlgAut_smul_eq_pull_degPts_of_coe_eq_qExpand.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.JHNeronObjectAtP.genOpH_U_add_ofAlgAut_smul_eq_pull_degPts_of_coe_eq_qExpand
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (S : Set ℕ)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]

    (αH βH : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    (hαq : ∀ u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)), ((αH u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβq : ∀ u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)), ((βH u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (αpull : Fin 2 → (JH (M / p) (ModularCurve.infSubgroup p M H hpM) →+ JH M H))

    (hdeg0 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) →
        O.degPts 0 (Pic0.mk Dv) = Pic0.mk Dw)
    (hpull1 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))))
        (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))),
      (Dv : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) = Divisor.pullbackAlong βH hβint (Dw : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) →
        αpull 1 (Pic0.mk Dw) = Pic0.mk Dv)

    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))) :
    ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p Fact.out hpM) x + SemilinearAut.ofAlgAut θ • x = αpull 1 (O.degPts 0 x) := by sorry
