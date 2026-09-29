-- Prove2me | Theorems.Thm_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
-- name    : ModularCurve.exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/fb4f2bbd-08f0-5fbd-b25a-6a4cea010b46
-- title:
--   Rational Atkin–Lehner automorphism at p ∥ M
-- statement:
--   Let $p$ be a prime, $M$ a nonzero natural number and $H \le (\mathbb{Z}/M)^\times$ a subgroup; assume $p \mid M$, $p^2 \nmid M$, and that every unit $u \in (\mathbb{Z}/M)^\times$ with trivial image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ lies in $H$. Write $H' =$ `infSubgroup p M H hpM` for the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, and for a subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ let $F(\Gamma) =$ `qExpFunctionFieldC ℚ Γ` be the subfield of $\mathbb{Q}(\!(q)\!)$ generated over $\mathbb{Q}$ by the quotients $\mathrm{intSeriesC}\,\mathbb{Q}\,p_f / \mathrm{intSeriesC}\,\mathbb{Q}\,p_g$ attached to pairs of modular forms $f,g$ of a common weight $k$ on the image $\Gamma_H$ of $H$ in $\mathrm{SL}_2(\mathbb{Z})$ (i.e. on [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133), the image under $\Gamma_0(M) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the upper-left-entry character $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$) with integral $q$-expansions $p_f, p_g$ and $\mathrm{intSeriesC}\,\mathbb{Q}\,p_g \ne 0$. The assertion is that there exists a $\mathbb{Q}$-algebra automorphism $\sigma$ of $F(\Gamma_H(M))$ with the following two properties. First, whenever $f \in F(\Gamma_H(M))$ and $u \in F(\Gamma_{H'}(M/p))$ have the same underlying Laurent series, the Laurent series of $\sigma f$ is $\mathrm{qExpand}\,\mathbb{Q}\,p$ applied to that of $u$, i.e. the substitution $q \mapsto q^p$ (the ring endomorphism of $\mathbb{Q}(\!(q)\!)$ multiplying all exponents by $p$). Second, for every unit $c \in (\mathbb{Z}/(M/p))^\times$ whose underlying residue is $p$, and all $f \in F(\Gamma_H(M))$, $u \in F(\Gamma_{H'}(M/p))$ with the Laurent series of $f$ equal to $u(q^p)$, the image of $\sigma f$ under the coefficient embedding $\mathbb{Q}(\!(q)\!) \to \overline{\mathbb{Q}}(\!(q)\!)$ equals the Laurent series of $\mathrm{diamondAutHBar}\,(M/p)\,H'\,c$ evaluated at the image of $u$ in `xHFunctionFieldBar (M / p) H'`, the subfield of $\overline{\mathbb{Q}}(\!(q)\!)$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of `xHFunctionField (M / p) H'`; here $\mathrm{diamondAutHBar}\,N\,H'\,c$ is an $\overline{\mathbb{Q}}$-automorphism of that field satisfying the predicate `IsDiamondAutHBar` — it sends a ratio of $q$-expansions $f/g$ to a ratio with $f, g$ replaced by $f|_k\gamma, g|_k\gamma$ for $\gamma \in \Gamma_0(N)$ with upper-left entry $\equiv c$ — chosen by choice, and taken to be the identity if no such automorphism exists.
--
--   This is the rational form of the Atkin–Lehner automorphism $w_p$ at a prime exactly dividing the level, realised on the $q$-expansion function field of $X_H(M)$, the model in which the cusp $\infty$ is rational: $w_p$ interchanges the two degeneracy pull-backs from level $M/p$, up to the diamond operator $\langle p \rangle$. It is used downstream in the constructions of charts, Ogg units and prolongation data on $X_H$ that enter the level-lowering arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    ∃ σ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ≃ₐ[ℚ]
        ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
      (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
          (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
          (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
            ((σ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) =
              qExpand ℚ p (u : LaurentSeries ℚ)) ∧
      (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (c : (ZMod (M / p))ˣ), (c : ZMod (M / p)) = (p : ZMod (M / p)) →
          ∀ (f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
            (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
            (f : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ) →
              coeffEmb (AlgebraicClosure ℚ)
                  ((σ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) =
                ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c
                    ⟨coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ),
                      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u.2⟩ :
                    ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
                  LaurentSeries (AlgebraicClosure ℚ))) := by sorry
