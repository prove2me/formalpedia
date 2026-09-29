-- Prove2me | Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_of_charP_of_dvd_div
-- name    : ModularCurve.finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_of_charP_of_dvd_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/081411bf-3f9d-56de-836e-911275cc99db
-- title:
--   Degree ℓ for the ℓ-degeneracy extension when ℓ∣ M/p
-- statement:
--   Let $K$ be an algebraically closed field of characteristic a prime $p$, let $M$ be a nonzero natural number with $p \mid M$ but $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$. Let $\ell$ be a prime with $\ell \mid M/p$ and $\ell \neq p$. Here, for a subgroup $\Gamma \le \mathrm{SL}(2,\mathbb{Z})$, the field [`ModularCurve.qExpFunctionFieldC K`](def/ModularCurve_X1.html#L101) $\Gamma$ is the intermediate field of $K$-Laurent series generated over $K$ by all quotients $\bar p_f/\bar p_g$, where $f,g$ are modular forms of some common weight $k$ for the image of $\Gamma$ in $\mathrm{GL}(2,\mathbb{R})$ admitting integral $q$-expansions $p_f,p_g \in \mathbb{Z}[[q]]$ with the image of $p_g$ in $K$ nonzero; and [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) is the subgroup of $\mathrm{SL}(2,\mathbb{Z})$ consisting of the elements of $\Gamma_0(M)$ whose lower-right entry reduces mod $M$ into $H$. The assertion is twofold: the inclusion [`ModularCurve.heckeAlphaModLH K M H ℓ`](def/ModularCurve_XHDifferentialsModL.html#L132) of the function field of $\Gamma_H(M)$ into that of $\Gamma_H(M) \cap \Gamma_0(M\ell)$ makes the latter a module of finite rank exactly $\ell$ over the former, and the relative degree of the same pair of intermediate fields of the Laurent series field equals $\ell$.
--
--   This is the degree of the $\ell$-degeneracy (roof) covering of the mod-$p$ function field of $X_H(M)$ in the case where $\ell$ divides $M/p$, so that the correspondence is of $U_\ell$ type and the degree is $\ell$ rather than $\ell+1$; the two conjuncts record the same degree in the two forms used later, as a finrank along the inclusion and as a relative degree of intermediate fields. It feeds the computation of reduced root functions for the Hecke correspondence at level $M$ in characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_of_charP_of_dvd_div.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups

theorem ModularCurve.finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_of_charP_of_dvd_div
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M / p) (hℓp : ℓ ≠ p) :
    (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      AlgebraicCurve.finrankAlong K (ModularCurve.heckeAlphaModLH K M H ℓ) = ℓ) ∧
    IntermediateField.relfinrank (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))
      (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) = ℓ := by sorry
