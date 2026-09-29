-- Prove2me | Theorems.Thm_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos
-- name    : ModularCurve.exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/052c5be6-9c52-57c2-b3dc-361bb1d3b479
-- title:
--   Elliptic places of X₀(M) mod ℓ and double cosets
-- statement:
--   Fix $M\ge 1$ and a subgroup $H\le(\mathbb{Z}/M)^\times$, let $\Gamma_H(M)\le \mathrm{SL}(2,\mathbb{Z})$ be the preimage in $\Gamma_0(M)$ of $H$ under the character $\gamma\mapsto d\bmod M$, let $\ell$ be a prime with $\ell\nmid M$ and let $K$ be an algebraically closed field of characteristic $\ell$. Write $F=\mathrm{qExpFunctionFieldC}\,K\,\Gamma_H(M)$ for the subfield of $K((q))$ generated over $K$ by the quotients $\mathrm{intSeriesC}\,K\,p_f/\mathrm{intSeriesC}\,K\,p_g$ of reductions of integral $q$-expansions $p_f,p_g$ at $\infty$ of modular forms $f,g$ of one weight on $\Gamma_H(M)$ (with $\mathrm{intSeriesC}\,K\,p_g\ne 0$), and $F_0=\mathrm{modularFunctionFieldFullC}\,K\,M$ for the subfield generated over $K$ by the series $\mathrm{qExpand}\,K\,d\,(\mathrm{jqModC}\,K)$ for the nonzero divisors $d\mid M$. Let $\rho:\Gamma_0(M)\to(F\simeq_{\mathrm{alg}[K]}F)$ be a homomorphism satisfying `IsDiamondPullbackModL`, i.e. for all $\gamma$, all weights $k$ and all forms $f,g,f_1,g_1$ on $\Gamma_H(M)$ with integral expansions $p_f,p_g,p_{f_1},p_{g_1}$ such that $f_1=f\mid_k\gamma$ and $g_1=g\mid_k\gamma$ as functions on $\mathbb{H}$ and $\mathrm{intSeriesC}\,K\,p_g\ne 0$, every $x\in F$ with underlying series $\mathrm{intSeriesC}\,K\,p_{f_1}/\mathrm{intSeriesC}\,K\,p_{g_1}$ has $\rho(\gamma)x$ equal to $\mathrm{intSeriesC}\,K\,p_f/\mathrm{intSeriesC}\,K\,p_g$; assume $F_0\le F$ and that each $\rho(\gamma)$ fixes every element of $F$ lying in $F_0$. Here a place of a field extension of $K$ is a valuation subring containing $K$, different from the whole field and a principal ideal ring, and $\mathrm{ord}$ denotes minus the logarithm of its associated adic valuation. The conclusion is a conjunction of two assertions. First, there is an injective map $\iota$ from the set of places $P$ of $F_0/K$ with $\mathrm{ord}_P(\bar\jmath)>0$, where $\bar\jmath=\mathrm{jqModC}\,K\in F_0$, to the double coset quotient $\Gamma_0(M)\backslash \mathrm{SL}(2,\mathbb{Z})/\langle ST\rangle$, such that whenever $\iota(P)$ is the double coset of $g$ and $\gamma\in\Gamma_0(M)$ satisfies $g^{-1}\gamma g\in\langle ST\rangle$, every place $Q$ of $F/K$ whose valuation subring pulls back along the inclusion $F_0\hookrightarrow F$ to that of $P$ is fixed by $\rho(\gamma)$. Second, the same statement with $\bar\jmath$ replaced by $\bar\jmath-1728$ and $\langle ST\rangle$ replaced by $\langle S\rangle$.
--
--   This is the mod-$\ell$ ($\ell\nmid M$) counterpart of the classical description of the elliptic points of $X_0(M)$: the places above $j=0$ and $j=1728$ are controlled by the double cosets of $\Gamma_0(M)$ in $\mathrm{SL}(2,\mathbb{Z})$ modulo the stabilisers $\langle ST\rangle$ and $\langle S\rangle$ of the fixed points $\rho$ and $i$, together with the statement that elements of $\Gamma_0(M)$ stabilising such a point act trivially, via the diamond operators, on the places of the function field of $X_H(M)$ above them. It is used in the count [`ModularCurve.card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset`](thm.html#ModularCurve.card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset) bounding the fibres of $\bar\jmath$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_XHDiamondModL
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularCurve.exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos
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
    (∃ ι : {P : AlgebraicCurve.Place K (ModularCurve.modularFunctionFieldFullC K M) //
              0 < P.ord (⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem_full K M⟩ :
                ModularCurve.modularFunctionFieldFullC K M)} →
            DoubleCoset.Quotient
              (CongruenceSubgroup.Gamma0 M : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
              (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) :
                Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
        Function.Injective ι ∧
        ∀ P (g : Matrix.SpecialLinearGroup (Fin 2) ℤ),
          ι P = DoubleCoset.mk (CongruenceSubgroup.Gamma0 M)
            (Subgroup.zpowers (ModularGroup.S * ModularGroup.T)) g →
          ∀ γ : CongruenceSubgroup.Gamma0 M,
            g⁻¹ * (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) * g ∈
              Subgroup.zpowers (ModularGroup.S * ModularGroup.T) →
            ∀ Q : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
              Q.toValuationSubring.comap (IntermediateField.inclusion hle).toRingHom =
                P.1.toValuationSubring →
              ρ γ • Q = Q) ∧
    (∃ ι : {P : AlgebraicCurve.Place K (ModularCurve.modularFunctionFieldFullC K M) //
              0 < P.ord ((⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem_full K M⟩ :
                ModularCurve.modularFunctionFieldFullC K M) -
                algebraMap K (ModularCurve.modularFunctionFieldFullC K M) 1728)} →
            DoubleCoset.Quotient
              (CongruenceSubgroup.Gamma0 M : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
              (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
        Function.Injective ι ∧
        ∀ P (g : Matrix.SpecialLinearGroup (Fin 2) ℤ),
          ι P = DoubleCoset.mk (CongruenceSubgroup.Gamma0 M) (Subgroup.zpowers ModularGroup.S) g →
          ∀ γ : CongruenceSubgroup.Gamma0 M,
            g⁻¹ * (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) * g ∈ Subgroup.zpowers ModularGroup.S →
            ∀ Q : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
              Q.toValuationSubring.comap (IntermediateField.inclusion hle).toRingHom =
                P.1.toValuationSubring →
              ρ γ • Q = Q) := by sorry
