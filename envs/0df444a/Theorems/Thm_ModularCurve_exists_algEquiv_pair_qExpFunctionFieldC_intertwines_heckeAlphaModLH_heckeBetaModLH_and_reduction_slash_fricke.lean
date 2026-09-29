-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_intertwines_heckeAlphaModLH_heckeBetaModLH_and_reduction_slash_fricke
-- name    : ModularCurve.exists_algEquiv_pair_qExpFunctionFieldC_intertwines_heckeAlphaModLH_heckeBetaModLH_and_reduction_slash_fricke
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/81ad35f1-2c66-5b89-9083-d8e6abea1cc8
-- title:
--   Mod-p Fricke involutions exchanging the two degeneracy maps
-- statement:
--   Let $p$ be a prime and $Q\ge 1$ with $p\nmid Q$, let $H'\le(\mathbb Z/Q)^\times$, let $K$ be an algebraically closed field of characteristic $p$, let $\varphi$ be a ring homomorphism from the integral closure $\overline{\mathbb Z}$ of $\mathbb Z$ in $\mathbb C$ to $K$, and let $q$ be a prime with $q\ne p$. Let $W_Q,W_{Qq}\in \mathrm{GL}_2(\mathbb R)$ have underlying matrices $\bigl(\begin{smallmatrix}0&-1\\ Q&0\end{smallmatrix}\bigr)$ and $\bigl(\begin{smallmatrix}0&-1\\ Qq&0\end{smallmatrix}\bigr)$. Write $\Gamma_{H'}(Q)\le \mathrm{SL}_2(\mathbb Z)$ for the group of matrices in $\Gamma_0(Q)$ whose lower-right entry, read as a unit of $\mathbb Z/Q$, lies in $H'$, and for a congruence subgroup $\Gamma$ let $F_K(\Gamma)\subseteq K(\!(X)\!)$ be the intermediate field generated over $K$ by all quotients $\overline{p_f}/\overline{p_g}$, where $f,g$ are modular forms of a common weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb R)$, $p_f,p_g\in\mathbb Z[\![X]\!]$ are integral power series whose complexifications are the width-one $q$-expansions of $f$ and $g$, the bar denotes coefficientwise reduction to $K$ viewed as a Laurent series, and $\overline{p_g}\ne 0$. The assertion is the existence of a $K$-algebra automorphism $\sigma$ of $F_K(\Gamma_{H'}(Q))$ and a $K$-algebra automorphism $\tau$ of $F_K(\Gamma_{H'}(Q)\cap\Gamma_0(Qq))$ such that: $\tau\circ\alpha=\beta\circ\sigma$ and $\tau\circ\beta=\alpha\circ\sigma$ pointwise, where $\alpha$ is the inclusion `heckeAlphaModLH` of $F_K(\Gamma_{H'}(Q))$ into $F_K(\Gamma_{H'}(Q)\cap\Gamma_0(Qq))$ and $\beta$ is `heckeBetaModLH`, given by the substitution $X\mapsto X^{q}$ on Laurent series when that substitution maps the smaller field into the larger one and by $\alpha$ otherwise; $\sigma\circ\sigma=\mathrm{id}$; and $\sigma$, respectively $\tau$, is the $\varphi$-reduction of slashing by $W_Q$, respectively $W_{Qq}$, in the following sense: for every weight $k$, all modular forms $f,g$ of weight $k$ for the relevant group, all $p_f,p_g\in\mathbb Z[\![X]\!]$ that are integral $q$-expansions of $f$ and $g$, every $D\in\mathbb N$ and all $P_f^W,P_g^W\in\overline{\mathbb Z}[\![X]\!]$ whose images in $\mathbb C[\![X]\!]$ are the width-one $q$-expansions of $D\cdot(f\mid_k W)$ and $D\cdot(g\mid_k W)$ (with $W=W_Q$ in the first clause, $W=W_{Qq}$ in the second), if $\overline{p_g}\ne 0$ and $\varphi(P_g^W)\ne 0$ as a Laurent series over $K$, then any element $x$ of the field whose underlying Laurent series is $\overline{p_f}/\overline{p_g}$ satisfies $\sigma(x)\cdot\varphi(P_g^W)=\varphi(P_f^W)$, respectively $\tau(x)\cdot\varphi(P_g^W)=\varphi(P_f^W)$.
--
--   This is the reduction to characteristic $p$ of the Fricke involutions on the modular curves $X_{H'}(Q)$ and $X(\Gamma_{H'}(Q)\cap\Gamma_0(Qq))$, realised concretely on the $q$-expansion function fields: the involution $\sigma$ interchanges the two degeneracy embeddings $\alpha$ and $\beta$ coming from the level-raising prime $q$, and its effect on ratios of reduced $q$-expansions is pinned down by slashing with $W_Q$ and $W_{Qq}$. It feeds the comparison of the Hecke action on differentials of the reduced curves that is used in the level-lowering argument at a prime $q$ not dividing the residual characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_intertwines_heckeAlphaModLH_heckeBetaModLH_and_reduction_slash_fricke.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_algEquiv_pair_qExpFunctionFieldC_intertwines_heckeAlphaModLH_heckeBetaModLH_and_reduction_slash_fricke
    (p Q : ℕ) [Fact p.Prime] [NeZero Q] (hpQ : ¬ p ∣ Q) (H' : Subgroup (ZMod Q)ˣ)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    (φ : ↥(integralClosure ℤ ℂ) →+* K)
    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p)
    (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (Q : ℝ), 0])
    (WQq : GL (Fin 2) ℝ) (hWQq : (WQq : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((Q * q : ℕ) : ℝ), 0]) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ∃ (σ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H')) ≃ₐ[K]
            ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H')))
      (τ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))) ≃ₐ[K]
            ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)))),

      (∀ x, τ (ModularCurve.heckeAlphaModLH K Q H' q x) = ModularCurve.heckeBetaModLH K Q H' q (σ x)) ∧

      (∀ x, τ (ModularCurve.heckeBetaModLH K Q H' q x) = ModularCurve.heckeAlphaModLH K Q H' q (σ x)) ∧

      (∀ x, σ (σ x) = x) ∧

      (∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH Q H' : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQ)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQ)) →
          ModularCurve.intSeriesC K pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ K (PgW.map φ) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H')),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg →
            ((σ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H'))) : LaurentSeries K) *
                HahnSeries.ofPowerSeries ℤ K (PgW.map φ) =
              HahnSeries.ofPowerSeries ℤ K (PfW.map φ)) ∧

      (∀ (k : ℤ) (f g : ModularForm ((CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q) :
              Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQq)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQq)) →
          ModularCurve.intSeriesC K pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ K (PgW.map φ) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg →
            ((τ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)))) :
                  LaurentSeries K) *
                HahnSeries.ofPowerSeries ℤ K (PgW.map φ) =
              HahnSeries.ofPowerSeries ℤ K (PfW.map φ)) := by sorry
