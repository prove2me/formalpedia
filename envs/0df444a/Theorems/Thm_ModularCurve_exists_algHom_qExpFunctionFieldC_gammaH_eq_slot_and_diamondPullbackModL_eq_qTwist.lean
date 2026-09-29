-- Prove2me | Theorems.Thm_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist
-- name    : ModularCurve.exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/3df3a0e3-aa0a-5307-ae4a-352ede86760b
-- title:
--   Mod ℓ cusp expansion of the function field of X_H(M)
-- statement:
--   Fix $M\ge 1$ and a subgroup $H\le(\mathbb Z/M)^\times$, and let $\Gamma_H(M)\le \mathrm{SL}(2,\mathbb Z)$ be the image of the subgroup of those $\gamma\in\Gamma_0(M)$ whose lower-right entry, as a unit of $\mathbb Z/M$, lies in $H$. Let $\ell$ be a prime with $\ell\nmid M$, let $K$ be an algebraically closed field of characteristic $\ell$, and let $\zeta\in K^\times$ be a primitive $M$-th root of unity. Write $F=$ `qExpFunctionFieldC K (CohCarrier.GammaH M H)` for the intermediate field of $K((q))$ generated over $K$ by the quotients $\overline{p_f}/\overline{p_g}$, where $f,g$ are modular forms of one and the same weight $k$ on $\Gamma_H(M)$, $p_f,p_g\in\mathbb Z[[q]]$ are integral power series whose images in $\mathbb C[[q]]$ are the level-one $q$-expansions of $f$ and $g$, and $\overline{p_g}\ne 0$ in $K((q))$. Let $\rho$ be a homomorphism from $\Gamma_0(M)$ to the group of $K$-algebra automorphisms of $F$ satisfying `IsDiamondPullbackModL`: for every $\gamma\in\Gamma_0(M)$, every weight $k$ and all forms $f,g,f_1,g_1$ of weight $k$ on $\Gamma_H(M)$ with integral expansions $p_f,p_g,p_{f_1},p_{g_1}$, if $f_1=f\mid_k\gamma$ and $g_1=g\mid_k\gamma$ as functions on $\mathbb H$ and $\overline{p_g}\ne0$, then $\rho(\gamma)$ carries the element of $F$ with Laurent series $\overline{p_{f_1}}/\overline{p_{g_1}}$ to the one with Laurent series $\overline{p_f}/\overline{p_g}$. Finally let $g\in \mathrm{SL}(2,\mathbb Z)$, $a\ge1$ an integer and $b\in\mathbb Z$ with $a\mid g_{10}$, $a\mid M$ and $g_{10}b\equiv g_{11}a \pmod M$. The assertion is that there exists a $K$-algebra homomorphism $\Theta: F\to K((q))$ such that: (1) every $x\in F$ whose Laurent series is the reduction $\bar\jmath$ of the $q$-expansion of $j$ satisfies $\Theta x=\bar\jmath(q^M)$; (2) every $x\in F$ whose Laurent series is $\bar\jmath(q^M)$ satisfies $\Theta x=(\mathrm{qTwist}(\zeta^{ba})\bar\jmath)(q^{a^2})$, where $\mathrm{qTwist}(u)$ multiplies the $k$-th coefficient by $u^k$ and $q\mapsto q^{a^2}$ is the substitution `qExpand K (a*a)`; and (3) for every $\gamma\in\Gamma_0(M)$ and $m\in\mathbb Z$ with $g^{-1}\gamma g=T^m$ or $g^{-1}\gamma g=-T^m$, one has $\Theta(\rho(\gamma^{-1})x)=\mathrm{qTwist}(\zeta^m)(\Theta x)$ for all $x\in F$.
--
--   This is the mod $\ell$ form of the expansion of the function field of $X_H(M)$ at the cusp $g\infty$ in the uniformiser $q_M=e^{2\pi i\tau/M}$: clauses (1) and (2) record the classical identities $j(g\tau)=\bar\jmath(q_M^M)$ and $j(Mg\tau)=\bar\jmath(\zeta^{ab}q_M^{a^2})$ coming from the Hermite normal form of $\mathrm{diag}(M,1)g$, while clause (3) says that the stabiliser of the cusp acts through $q_M\mapsto\zeta^m q_M$. It feeds the construction of the places of the mod $\ell$ function field attached to double cosets and of the valuations used there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_XHDiamondModL
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularCurve.exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M)
    (ρ : CongruenceSubgroup.Gamma0 M →*
      (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)))
    (hρ : ModularCurve.IsDiamondPullbackModL K M H ρ)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (a : ℕ) [NeZero a] (b : ℤ)
    (ha : (a : ℤ) ∣ g 1 0) (haM : a ∣ M) (hb : g 1 0 * b ≡ g 1 1 * a [ZMOD M]) :
    ∃ Θ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] LaurentSeries K,
      (∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
        (x : LaurentSeries K) = ModularCurve.jqModC K →
          Θ x = ModularCurve.qExpand K M (ModularCurve.jqModC K)) ∧
      (∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
        (x : LaurentSeries K) = ModularCurve.jqNModC K M →
          Θ x = ModularCurve.qExpand K (a * a)
            (ModularCurve.qTwist (ζ ^ (b * (a : ℤ))) (ModularCurve.jqModC K))) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M) (m : ℤ),
        (g⁻¹ * (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) * g = ModularGroup.T ^ m ∨
          g⁻¹ * (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) * g = -(ModularGroup.T ^ m)) →
        ∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
          Θ (ρ γ⁻¹ x) = ModularCurve.qTwist (ζ ^ m) (Θ x)) := by sorry
