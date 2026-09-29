-- Prove2me | Theorems.Thm_ModularCurve_IsInfReductionMap_exists_smul_correspondence_heckeAlphaModLH_heckeBetaModLH_apply_eq_of_ne
-- name    : ModularCurve.IsInfReductionMap.exists_smul_correspondence_heckeAlphaModLH_heckeBetaModLH_apply_eq_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/64f16a47-091d-58dc-8efc-f890b1466ecf
-- title:
--   Transposed Hecke correspondence at q ≠ p after mod p reduction
-- statement:
--   Let $p$ be a prime and $M \ge 1$ with $p \mid M$ and $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is $1$. Let $K$ be an algebraically closed field which is a $\mathbb{Z}/p$-algebra, write $H'$ for the image [`ModularCurve.infSubgroup p M H hpM`](def/ModularCurve_XHDifferentialsModL.html#L246) of $H$ in $(\mathbb{Z}/(M/p))^\times$, and let $\rho$ be a $K$-linear map from $K \otimes_{\mathbb{Z}/p}$ [`CuspForm.IntTwoCuspForms M H p`](def/ModularCurve_XHDifferentialsModL.html#L374) to $\Omega_{F/K}$, where $F =$ [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M/p) H')`](def/ModularCurve_X1.html#L101), satisfying [`ModularCurve.IsInfReductionMap`](def/ModularCurve_XHDifferentialsModL.html#L443): for every weight-$2$ cusp form $f$ on $\Gamma_H(M)$ lying in [`CuspForm.twoCuspIntegralSet M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L54) (all $q$-expansion coefficients of $tf$ and of the Atkin–Lehner slash of $tf$ lie in the prime subring of $\mathbb{C}$, for every $t$ in the Hecke ring and every Atkin–Lehner datum at $p$) and every integral power series $P_f$ with `IsIntegralQExp f pf`, the $q$-expansion `diffQExp` of $\rho(1 \otimes \bar f)$ is the reduction of $P_f$. Let $q$ be a prime with $q \mid M$, $q \neq p$, and let $f$ be such a two-cusp integral weight-$2$ cusp form on $\Gamma_H(M)$. Then there are a natural number $D$ with $p \nmid D$ and a weight-$2$ cusp form $g$ on $\Gamma_H(M)$, again in [`CuspForm.twoCuspIntegralSet M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L54), such that, as functions on the upper half-plane, $g = D \sum_{j=0}^{q-1} f \mid_2 \bigl(\mathrm{heckeDiagMatrix}\, q \cdot {}^{t}(T^{Mj})\bigr)$, and such that $D$ times $\operatorname{tr}_\alpha \circ \beta^{*}$ applied to $\rho(1 \otimes \bar f)$ equals $\rho(1 \otimes \bar g)$, where $\alpha =$ [`ModularCurve.heckeAlphaModLH K (M/p) H' q`](def/ModularCurve_XHDifferentialsModL.html#L132) is the inclusion of $F$ into the $q$-expansion function field of $\Gamma_{H'}(M/p) \cap \Gamma_0((M/p)q)$ over $K$, $\beta =$ [`ModularCurve.heckeBetaModLH K (M/p) H' q`](def/ModularCurve_XHDifferentialsModL.html#L167) is the second degeneracy embedding, and $\operatorname{tr}_\alpha \circ \beta^{*}$ is [`AlgebraicCurve.Differential.correspondence`](def/AlgebraicCurve_DifferentialPushPull.html#L69) for this pair, namely the trace along $\alpha$ composed after pullback along $\beta$ on Kähler differentials.
--
--   This is the transposed companion, for a prime $q \neq p$ dividing the level, of the compatibility of reduction modulo $p$ with the Hecke operator $U_q$ on the component through infinity of the special fibre: the transpose of $U_q$ acts on differentials as the correspondence $\operatorname{tr}_\alpha \circ \beta^{*}$, and on two-cusp integral forms it is realised, up to a prime-to-$p$ factor, by the sum of slashes by $\mathrm{diag}(q,1)\,{}^{t}T^{Mj}$. It is used by [`ModularCurve.twist_correspondence_heckeU_eq_genDiffModL_U_of_atkinLehnerPinAlong_of_ne`](thm.html#ModularCurve.twist_correspondence_heckeU_eq_genDiffModL_U_of_atkinLehnerPinAlong_of_ne) in the analysis of Hecke action on differentials used for level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsInfReductionMap_exists_smul_correspondence_heckeAlphaModLH_heckeBetaModLH_apply_eq_of_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups ModularForm

theorem ModularCurve.IsInfReductionMap.exists_smul_correspondence_heckeAlphaModLH_heckeBetaModLH_apply_eq_of_ne
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]
    {ρ : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
        Ω[ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]}
    (hρ : ModularCurve.IsInfReductionMap K p M H hpM ρ)
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p)
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    ∃ (D : ℕ) (_ : ¬ p ∣ D) (g : CuspForm (CohCarrier.GammaH M H) 2)
      (hg : g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)),
      (⇑g = (D : ℂ) • ∑ j ∈ Finset.range q,
          (⇑f) ∣[(2 : ℤ)] (ModularForm.heckeDiagMatrix q *
            (Matrix.SpecialLinearGroup.mapGL ℝ
              (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ))) ∧
      (haveI : NeZero q := ⟨hq.ne_zero⟩;
        (D : K) • AlgebraicCurve.Differential.correspondence
            (ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q)
            (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q)
            (ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
              ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)) =
          ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
            ⟨g, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hg⟩)) := by sorry
