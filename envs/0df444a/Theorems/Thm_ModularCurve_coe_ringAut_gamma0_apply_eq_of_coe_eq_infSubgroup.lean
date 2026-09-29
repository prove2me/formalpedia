-- Prove2me | Theorems.Thm_ModularCurve_coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup
-- name    : ModularCurve.coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/02546605-bbc7-5cd2-8d1d-8f7c879bc12d
-- title:
--   Compatibility of rational diamond actions at levels M and M/p
-- statement:
--   Let $p$ be a prime and $M\ge 1$ with $p\mid M$ and $M/p\ne 0$, and let $H\le(\mathbb Z/M)^\times$. Write $\Gamma_H(M)\le\mathrm{SL}_2(\mathbb Z)$ for the image in $\mathrm{SL}_2(\mathbb Z)$ of the preimage of $H$ under the homomorphism $\Gamma_0(M)\to(\mathbb Z/M)^\times$ given by reducing the lower right entry, and let $H'=$ `infSubgroup p M H hpM` be the image of $H$ under the reduction $(\mathbb Z/M)^\times\to(\mathbb Z/(M/p))^\times$. For a subgroup $\Gamma$, `qExpFunctionFieldC ℚ Γ` denotes the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the quotients $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$, where $f,g$ are weight-$k$ modular forms for $\Gamma$ whose $q$-expansions come from integral power series $p_f,p_g$ and $\mathrm{intSeriesC}(p_g)\ne 0$. Given monoid homomorphisms $\rho_M$ from $\Gamma_0(M)$ and $\rho_N$ from $\Gamma_0(M/p)$ to the ring automorphism groups of `qExpFunctionFieldC ℚ (GammaH M H)` and of `qExpFunctionFieldC ℚ (GammaH (M/p) H')` respectively, each assumed to be trivial on the elements lying in the corresponding $\Gamma_H$, and each assumed to satisfy the slash formula: whenever $f,g,f_1,g_1$ are weight-$k$ forms for the relevant $\Gamma_H$ with integral expansion witnesses $p_f,p_g,p_{f_1},p_{g_1}$, $c\in\mathbb C^\times$, $f_1=c\,(f\mid_k\gamma)$ and $g_1=c\,(g\mid_k\gamma)$ as functions on $\mathbb H$, and $\mathrm{intSeriesC}(p_g)\ne0\ne\mathrm{intSeriesC}(p_{g_1})$, then the automorphism attached to $\gamma$ sends $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$ to $\mathrm{intSeriesC}(p_{f_1})/\mathrm{intSeriesC}(p_{g_1})$. Then for $\gamma\in\Gamma_0(M)$ and $\gamma'\in\Gamma_0(M/p)$ with the same underlying matrix, and for $f$ in the level-$M$ field and $u$ in the level-$(M/p)$ field with the same Laurent series, $\rho_M(\gamma)f$ and $\rho_N(\gamma')u$ have the same image in $\mathbb Q((q))$.
--
--   This is the statement that the rational diamond action on the function field of $X_H(M)$ restricts, along the inclusion of function fields coming from $\Gamma_H(M)\le\Gamma_{H'}(M/p)$, to the diamond action at level $M/p$. It is used for the comparison of diamond automorphisms on the two levels and in the construction of generic charts for the Atkin–Lehner data on the reduction model of $X_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open ModularCurve

open scoped ModularForm in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.coe_ringAut_gamma0_apply_eq_of_coe_eq_infSubgroup
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (ρM : CongruenceSubgroup.Gamma0 M →* RingAut ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hρM_H : ∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρM γ = 1)
    (hρM_slash : (∀ (γ : CongruenceSubgroup.Gamma0 M) {k : ℤ}
      (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
      {pf pg pf₁ pg₁ : PowerSeries ℤ} (c : ℂ) (_ : c ≠ 0)
      (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
      (_ : IsIntegralQExp f₁ pf₁) (_ : IsIntegralQExp g₁ pg₁)
      (_ : (⇑f₁ : UpperHalfPlane → ℂ) = c • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
      (_ : (⇑g₁ : UpperHalfPlane → ℂ) = c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
      (hg0 : intSeriesC ℚ pg ≠ 0) (_ : intSeriesC ℚ pg₁ ≠ 0),
      ((ρM γ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
          ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = intSeriesC ℚ pf₁ / intSeriesC ℚ pg₁))
    (ρN : CongruenceSubgroup.Gamma0 (M / p) →*
      RingAut ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))
    (hρN_H : ∀ γ : CongruenceSubgroup.Gamma0 (M / p),
      (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) → ρN γ = 1)
    (hρN_slash : (∀ (γ : CongruenceSubgroup.Gamma0 (M / p)) {k : ℤ}
      (f g f₁ g₁ : ModularForm (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ)) k)
      {pf pg pf₁ pg₁ : PowerSeries ℤ} (c : ℂ) (_ : c ≠ 0)
      (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
      (_ : IsIntegralQExp f₁ pf₁) (_ : IsIntegralQExp g₁ pg₁)
      (_ : (⇑f₁ : UpperHalfPlane → ℂ) = c • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
      (_ : (⇑g₁ : UpperHalfPlane → ℂ) = c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
      (hg0 : intSeriesC ℚ pg ≠ 0) (_ : intSeriesC ℚ pg₁ ≠ 0),
      ((ρN γ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
          ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) : LaurentSeries ℚ) = intSeriesC ℚ pf₁ / intSeriesC ℚ pg₁))
    (γ : CongruenceSubgroup.Gamma0 M) (γ' : CongruenceSubgroup.Gamma0 (M / p)) (hγ : (γ : SL(2, ℤ)) = (γ' : SL(2, ℤ)))
    (f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))))
    (hfu : (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ)) :
    ((ρM γ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) =
      ((ρN γ' u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))) : LaurentSeries ℚ) := by sorry
