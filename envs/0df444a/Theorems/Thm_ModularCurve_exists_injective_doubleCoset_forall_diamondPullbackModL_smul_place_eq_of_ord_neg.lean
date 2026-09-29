-- Prove2me | Theorems.Thm_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_neg
-- name    : ModularCurve.exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/7aecd816-8713-51ab-a70c-827980bb927e
-- title:
--   Cusp places inject into double cosets, with trivial diamond stabilisers
-- statement:
--   Let $M\ge 1$, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, let $\ell$ be a prime with $\ell\nmid M$, and let $K$ be an algebraically closed field of characteristic $\ell$. Write $F_0=$ [`ModularCurve.modularFunctionFieldFullC K M`](def/ModularCurve_X0ModL.html#L100) for the subfield of $K((q))$ generated over $K$ by the series $\mathrm{qExpand}_K^{\,d}(\bar\jmath)$ for the nonzero divisors $d\mid M$, where $\bar\jmath=$ [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15) is $q^{-1}$ times the reduction to $K$ of the integral power series $\mathrm{jNum}$, and write $F=$ [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)`](def/ModularCurve_X1.html#L101) for the subfield of $K((q))$ generated over $K$ by the quotients of reductions to $K$ of integral $q$-expansions at $\infty$ of pairs of modular forms of a common weight on $\Gamma_H(M)$, the group of matrices in $\Gamma_0(M)$ whose lower-right entry lies in $H$ modulo $M$ (denominators taken with nonzero reduction). Let $\rho$ be a homomorphism from $\Gamma_0(M)$ to the group of $K$-algebra automorphisms of $F$ satisfying [`ModularCurve.IsDiamondPullbackModL`](def/ModularCurve_XHDiamondModL.html#L12): whenever $f_1=f\mid_k\gamma$ and $g_1=g\mid_k\gamma$ for forms of weight $k$ on $\Gamma_H(M)$ with integral expansions $p_f,p_g,p_{f_1},p_{g_1}$ and the reduction of $p_g$ is nonzero, $\rho(\gamma)$ sends the element of $F$ given by the reduction of $p_{f_1}/p_{g_1}$ to that of $p_f/p_g$. Assume in addition $F_0\le F$ and that $\rho(\gamma)$ fixes every element of $F$ whose Laurent series lies in $F_0$, for all $\gamma\in\Gamma_0(M)$. Then there is an injective map $\iota$ from the set of places $P$ of $F_0$ over $K$ (valuation subrings of $F_0$ that contain $K$, are not everything, and are principal ideal rings) with $P.\mathrm{ord}(\bar\jmath)<0$ to the double coset space $\Gamma_0(M)\backslash \mathrm{SL}(2,\mathbb{Z})/\langle T,-1\rangle$, where $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$ and $\langle T,-1\rangle$ is the join of the subgroups of integral powers of $T$ and of $-1$, with the following property: if $\iota(P)$ is the class of $g\in\mathrm{SL}(2,\mathbb{Z})$ and $\gamma\in\Gamma_0(M)$ satisfies $g^{-1}\gamma g\in\langle T,-1\rangle$, then every place $Q$ of $F$ over $K$ whose valuation subring pulls back along the inclusion $F_0\hookrightarrow F$ to that of $P$ is fixed by $\rho(\gamma)$, i.e. $\rho(\gamma)\cdot Q=Q$.
--
--   In the function-field model of modular curves in characteristic $\ell\nmid M$ this is the statement that the cusps of $X_0(M)_K$ — the poles of $\bar\jmath$ — inject into $\Gamma_0(M)\backslash\mathbb{P}^1(\mathbb{Q})=\Gamma_0(M)\backslash\mathrm{SL}(2,\mathbb{Z})/\langle T,-1\rangle$, together with the assertion that the stabiliser in $\Gamma_0(M)$ of such a cusp acts trivially, through the reduced diamond operators, on the places of $X_H(M)_K$ above it. It feeds the comparison [`ModularCurve.card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset`](thm.html#ModularCurve.card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset), which bounds the number of places of $F$ above a cuspidal place of $F_0$ by the size of the double coset space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_neg.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_XHDiamondModL
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularCurve.exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_neg
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (ρ : CongruenceSubgroup.Gamma0 M →*
      (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)))
    (hρ : ModularCurve.IsDiamondPullbackModL K M H ρ)
    (hle : ModularCurve.modularFunctionFieldFullC K M ≤
      ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hfix : ∀ (γ : CongruenceSubgroup.Gamma0 M)
      (x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
      (x : LaurentSeries K) ∈ ModularCurve.modularFunctionFieldFullC K M → ρ γ x = x) :
    ∃ ι : {P : AlgebraicCurve.Place K (ModularCurve.modularFunctionFieldFullC K M) //
              P.ord (⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem_full K M⟩ :
                ModularCurve.modularFunctionFieldFullC K M) < 0} →
            DoubleCoset.Quotient
              (CongruenceSubgroup.Gamma0 M : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
              ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) :
                  Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
                Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
        Function.Injective ι ∧
        ∀ P (g : Matrix.SpecialLinearGroup (Fin 2) ℤ),
          ι P = DoubleCoset.mk (CongruenceSubgroup.Gamma0 M)
            (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1)) g →
          ∀ γ : CongruenceSubgroup.Gamma0 M,
            g⁻¹ * (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) * g ∈
              Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) →
            ∀ Q : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
              Q.toValuationSubring.comap (IntermediateField.inclusion hle).toRingHom =
                P.1.toValuationSubring →
              ρ γ • Q = Q := by sorry
