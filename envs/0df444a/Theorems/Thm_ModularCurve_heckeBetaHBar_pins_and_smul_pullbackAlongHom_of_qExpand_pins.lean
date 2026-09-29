-- Prove2me | Theorems.Thm_ModularCurve_heckeBetaHBar_pins_and_smul_pullbackAlongHom_of_qExpand_pins
-- name    : ModularCurve.heckeBetaHBar_pins_and_smul_pullbackAlongHom_of_qExpand_pins
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/89175de1-39ba-56cf-a2b6-06d87c3cc003
-- title:
--   Pinned automorphism intertwines degeneracy maps and divisor-class pullback
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ and $M/p \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and write $H' =$ `infSubgroup p M H hpM` for the image of $H$ under the reduction $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$. Assume `HeckeBetaHDefined (M/p) H' p`, i.e. that $y \mapsto y(q^p)$ (the `qExpand` substitution on Laurent series) carries `xHFunctionField (M/p) H'` into `xHTopFunctionFieldC ℚ (M/p) H' (M/p*p)`, and that the function field $\bar F_M :=$ `xHFunctionFieldBar M H` has principal divisors of degree zero. Let $\iota$ be an $\overline{\mathbb{Q}}$-algebra map from the base-changed roof field $\bar F^{\mathrm{top}} :=$ `laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M/p) H' (M/p*p))` to $\bar F_M$ which is the identity on underlying Laurent series, is integral, satisfies the fundamental identity `FundamentalIdentityAlong` along $\iota$ (sum of ramification indices times residue degrees over each fibre equals the field degree times the degree of the place), and is surjective. Let $pb \in (\mathbb{Z}/(M/p))^{\times}$ reduce to $p$, and let $\theta$ be an $\overline{\mathbb{Q}}$-algebra automorphism of $\bar F_M$ subject to two $q$-expansion pins: if $f \in \bar F_M$ has the same Laurent series as $u \in \bar F_{M/p} :=$ `xHFunctionFieldBar (M/p) H'`, then the series of $\theta f$ is $u(q^p)$; and for every unit $c$ reducing to $p$, if the series of $f$ is $u(q^p)$, then the series of $\theta f$ is that of `diamondAutHBar (M/p) H' c u`. Putting $\iota_e$ for the algebra isomorphism $\bar F^{\mathrm{top}} \simeq \bar F_M$ determined by $\iota$ and $W := \iota_e^{-1} \circ \theta^{-1} \circ \iota_e$, an automorphism of $\bar F^{\mathrm{top}}$, the conclusion is threefold: $W \circ \beta = \alpha$ and $W \circ \alpha = \beta \circ \langle pb \rangle^{-1}$ pointwise on $\bar F_{M/p}$, where $\alpha =$ `heckeAlphaHBar (AlgebraicClosure ℚ) (M/p) H' p` is the inclusion of $\bar F_{M/p}$ into $\bar F^{\mathrm{top}}$, $\beta =$ `heckeBetaHBar (AlgebraicClosure ℚ) (M/p) H' p` is the map induced by $q \mapsto q^p$ (available by the hypothesis above) and $\langle pb \rangle =$ `diamondAutHBar (M/p) H' pb`; and, for every class $x_1 \in \mathrm{Pic}^0(\bar F^{\mathrm{top}})$, the semilinear action of $\theta$ (via `SemilinearAut.ofAlgAut`, trivial on $\overline{\mathbb{Q}}$) on the pullback `Pic0.pullbackAlongHom ι hι hFIι x₁` equals the pullback of the action of $W^{-1}$ on $x_1$.
--
--   This is the Atkin–Lehner automorphism at $p$, read on the roof $\Gamma_{H'}(M/p) \cap \Gamma_0(M)$ identified with level $\Gamma_H(M)$: it exchanges the two degeneracy legs up to the diamond operator $\langle p \rangle$, and it transports degree-zero divisor classes compatibly with the pullback along the roof identification. The three conclusions are exactly the hypotheses on $W$ needed for the level-$\Gamma_H$ relation between $U_p$, the Atkin–Lehner twist and the composite of the degeneracy pullback and pushforward, used by [`ModularCurve.JHNeronObjectAtP.genOpH_U_add_ofAlgAut_smul_eq_pull_degPts_of_coe_eq_qExpand`](thm.html#ModularCurve.JHNeronObjectAtP.genOpH_U_add_ofAlgAut_smul_eq_pull_degPts_of_coe_eq_qExpand).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeBetaHBar_pins_and_smul_pullbackAlongHom_of_qExpand_pins.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_ShimuraKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.heckeBetaHBar_pins_and_smul_pullbackAlongHom_of_qExpand_pins
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hβN : ModularCurve.HeckeBetaHDefined (M / p) (ModularCurve.infSubgroup p M H hpM) p)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]
    (ι : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))) →ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.xHFunctionFieldBar M H))
    (hιcoe : ∀ u : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))),
      ((ι u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hι : ι.toRingHom.IsIntegral) (hFIι : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hι)
    (hιs : Function.Surjective ι)
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθ₂ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∀ (c : (ZMod (M / p))ˣ), (c : ZMod (M / p)) = (p : ZMod (M / p)) →
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ))) :
    let ιe : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.xHFunctionFieldBar M H) := AlgEquiv.ofBijective ι ⟨ι.toRingHom.injective, hιs⟩
    let W := (ιe.trans θ.symm).trans ιe.symm
    (∀ x : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)),
        W (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p x) =
          ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p x) ∧
    (∀ x : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)),
        W (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p x) =
          ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p
            ((ModularCurve.diamondAutHBar (M / p) (ModularCurve.infSubgroup p M H hpM) pb).symm x)) ∧
    (∀ x₁ : Pic0 (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))),
      SemilinearAut.ofAlgAut θ • Pic0.pullbackAlongHom ι hι hFIι x₁ =
        Pic0.pullbackAlongHom ι hι hFIι (SemilinearAut.ofAlgAut W.symm • x₁)) := by sorry
