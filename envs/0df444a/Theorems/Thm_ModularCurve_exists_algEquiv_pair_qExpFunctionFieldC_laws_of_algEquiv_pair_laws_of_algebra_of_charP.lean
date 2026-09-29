-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP
-- name    : ModularCurve.exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/fa458e92-5aba-5791-9954-a2c56109f934
-- title:
--   Base change κ⊆ K of a Fricke automorphism pair
-- statement:
--   Fix a prime $p$, a natural number $Q$ with $Q\neq 0$ and a subgroup $H'\le(\mathbb{Z}/Q)^{\times}$; let $K$ be an algebraically closed field of characteristic $p$ and $\kappa$ a field equipped with an algebra map $\kappa\to K$. Let $q$ be a prime, and assume $Q$ and $q$ are non-zero in $K$, and that [`ModularCurve.HeckeBetaModLHDefined`](def/ModularCurve_XHDifferentialsModL.html#L143) holds over $\kappa$ and over $K$, i.e. the exponent-scaling map `qExpand` by $q$ carries the $q$-expansion field $F_\kappa:=$ `qExpFunctionFieldC` of level [`CohCarrier.GammaH Q H'`](def/CohCarrier_Level.html#L133) into the field $F'_\kappa$ of level [`CohCarrier.GammaH Q H' ⊓ Gamma0 (Q*q)`](def/CohCarrier_Level.html#L133) (likewise over $K$); here `qExpFunctionFieldC K Γ` is the intermediate field of `LaurentSeries K` generated over $K$ by all quotients `intSeriesC K pf / intSeriesC K pg` with non-zero denominator, $p_f,p_g$ integral power series whose images in $\mathbb{C}[[X]]$ are the width-$1$ $q$-expansions of two weight-$k$ modular forms on $\Gamma$. Let $\varphi_\kappa$ be a ring homomorphism from the algebraic integers $\overline{\mathbb{Z}}=$ `integralClosure ℤ ℂ` to $\kappa$, and let $W_Q,W_{Qq}\in\mathrm{GL}_2(\mathbb{R})$ have matrices $\begin{pmatrix}0&-1\\ Q&0\end{pmatrix}$ and $\begin{pmatrix}0&-1\\ Qq&0\end{pmatrix}$. Suppose given a $\kappa$-algebra automorphism $\sigma_\kappa$ of $F_\kappa$ and a $\kappa$-algebra automorphism $\tau_\kappa$ of $F'_\kappa$ satisfying five laws: $\tau_\kappa\circ\alpha=\beta\circ\sigma_\kappa$ and $\tau_\kappa\circ\beta=\alpha\circ\sigma_\kappa$, where $\alpha=$ `heckeAlphaModLH` is the inclusion $F_\kappa\hookrightarrow F'_\kappa$ and $\beta=$ `heckeBetaModLH` is the $q$-scaling map; $\sigma_\kappa\circ\sigma_\kappa=\mathrm{id}$; and two Fricke reduction specifications, namely for every weight $k$, forms $f,g$ of weight $k$ on [`CohCarrier.GammaH Q H'`](def/CohCarrier_Level.html#L133) (respectively on [`CohCarrier.GammaH Q H' ⊓ Gamma0 (Q*q)`](def/CohCarrier_Level.html#L133)), integral power series $p_f,p_g$ realising their $q$-expansions, $D\in\mathbb{N}$ and power series $P^W_f,P^W_g$ over $\overline{\mathbb{Z}}$ whose images in $\mathbb{C}[[X]]$ are the $q$-expansions of $D\cdot(f\mid_k W_Q)$ and $D\cdot(g\mid_k W_Q)$ (respectively $W_{Qq}$), with `intSeriesC κ pg` $\neq0$ and the Laurent series of $\varphi_\kappa(P^W_g)$ non-zero, every $x$ in the field whose underlying Laurent series is `intSeriesC κ pf / intSeriesC κ pg` satisfies $\sigma_\kappa(x)\cdot\varphi_\kappa(P^W_g)=\varphi_\kappa(P^W_f)$ (respectively $\tau_\kappa(x)\cdot\varphi_\kappa(P^W_g)=\varphi_\kappa(P^W_f)$) in `LaurentSeries κ`. The conclusion asserts the existence of a $K$-algebra automorphism $\sigma$ of the $q$-expansion field over $K$ of level [`CohCarrier.GammaH Q H'`](def/CohCarrier_Level.html#L133) and a $K$-algebra automorphism $\tau$ of the one of level [`CohCarrier.GammaH Q H' ⊓ Gamma0 (Q*q)`](def/CohCarrier_Level.html#L133) satisfying the same five laws over $K$, the two reduction specifications being read along the composite $\varphi=(\kappa\to K)\circ\varphi_\kappa$.
--
--   This is the constant-field base-change step for the Fricke pair of automorphisms of the $q$-expansion function fields in characteristic $p$: a pair of automorphisms intertwining the degeneracy inclusion with the $q$-power substitution, and normalised by prescribed reductions of Fricke-twisted $q$-expansions, is transported from a subfield $\kappa$ of constants to the algebraically closed field $K$. It feeds the assembly of [`ModularCurve.exists_algEquiv_pair_qExpFunctionFieldC_intertwines_heckeAlphaModLH_heckeBetaModLH_and_reduction_slash_fricke`](thm.html#ModularCurve.exists_algEquiv_pair_qExpFunctionFieldC_intertwines_heckeAlphaModLH_heckeBetaModLH_and_reduction_slash_fricke), which supplies the Fricke/Atkin–Lehner data used in the level-lowering arguments for mod-$p$ modular representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP
    (p Q : ℕ) [Fact p.Prime] [NeZero Q] (H' : Subgroup (ZMod Q)ˣ)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    (κ : Type*) [Field κ] [Algebra κ K]
    (q : ℕ) (hq : q.Prime) (hQK : ((Q : ℕ) : K) ≠ 0) (hqK : ((q : ℕ) : K) ≠ 0)
    (hβκ : haveI : NeZero q := ⟨hq.ne_zero⟩; ModularCurve.HeckeBetaModLHDefined κ Q H' q)
    (hβK : haveI : NeZero q := ⟨hq.ne_zero⟩; ModularCurve.HeckeBetaModLHDefined K Q H' q)
    (φκ : ↥(integralClosure ℤ ℂ) →+* κ)
    (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (Q : ℝ), 0])
    (WQq : GL (Fin 2) ℝ) (hWQq : (WQq : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((Q * q : ℕ) : ℝ), 0])
    (σκ : haveI : NeZero q := ⟨hq.ne_zero⟩;
      ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H')) ≃ₐ[κ] ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H')))
    (τκ : haveI : NeZero q := ⟨hq.ne_zero⟩;
      ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))) ≃ₐ[κ]
        ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))))
    (hκ : haveI : NeZero q := ⟨hq.ne_zero⟩;

      (∀ x, τκ (ModularCurve.heckeAlphaModLH κ Q H' q x) = ModularCurve.heckeBetaModLH κ Q H' q (σκ x)) ∧

      (∀ x, τκ (ModularCurve.heckeBetaModLH κ Q H' q x) = ModularCurve.heckeAlphaModLH κ Q H' q (σκ x)) ∧

      (∀ x, σκ (σκ x) = x) ∧

      (∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH Q H' : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQ)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQ)) →
          ModularCurve.intSeriesC κ pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ κ (PgW.map φκ) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H')),
            (x : LaurentSeries κ) = ModularCurve.intSeriesC κ pf / ModularCurve.intSeriesC κ pg →
            ((σκ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H'))) : LaurentSeries κ) *
                HahnSeries.ofPowerSeries ℤ κ (PgW.map φκ) =
              HahnSeries.ofPowerSeries ℤ κ (PfW.map φκ)) ∧

      (∀ (k : ℤ) (f g : ModularForm ((CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q) :
              Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQq)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQq)) →
          ModularCurve.intSeriesC κ pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ κ (PgW.map φκ) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))),
            (x : LaurentSeries κ) = ModularCurve.intSeriesC κ pf / ModularCurve.intSeriesC κ pg →
            ((τκ x : ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)))) :
                  LaurentSeries κ) *
                HahnSeries.ofPowerSeries ℤ κ (PgW.map φκ) =
              HahnSeries.ofPowerSeries ℤ κ (PfW.map φκ))) :
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
          HahnSeries.ofPowerSeries ℤ K (PgW.map ((algebraMap κ K).comp φκ)) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H')),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg →
            ((σ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H'))) : LaurentSeries K) *
                HahnSeries.ofPowerSeries ℤ K (PgW.map ((algebraMap κ K).comp φκ)) =
              HahnSeries.ofPowerSeries ℤ K (PfW.map ((algebraMap κ K).comp φκ))) ∧

      (∀ (k : ℤ) (f g : ModularForm ((CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q) :
              Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQq)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQq)) →
          ModularCurve.intSeriesC K pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ K (PgW.map ((algebraMap κ K).comp φκ)) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg →
            ((τ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)))) :
                  LaurentSeries K) *
                HahnSeries.ofPowerSeries ℤ K (PgW.map ((algebraMap κ K).comp φκ)) =
              HahnSeries.ofPowerSeries ℤ K (PfW.map ((algebraMap κ K).comp φκ))) := by sorry
