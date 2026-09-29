-- Prove2me | Theorems.Thm_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_baseChange_tateModule_jH
-- name    : ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_baseChange_tateModule_jH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/c68668f8-86ab-556f-a666-ac65dcab48c7
-- title:
--   Parabolic H¹ with 𝒪-coefficients as dual of 𝒪⊗ Tₚ J_H
-- statement:
--   Let $M\ge 1$ and let $p$ be a prime, let $H\le(\mathbb Z/M)^\times$ be a subgroup and $S\subseteq\mathbb N$ an arbitrary set, and assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113), i.e. that for every prime $\ell$ the predicate `HeckeInputsHAlong` holds over $\overline{\mathbb Q}$ for $M,H,\ell$, and that for every $d\in(\mathbb Z/M)^\times$ there is an automorphism $\sigma$ of the function field `xHFunctionFieldBar M H` over $\overline{\mathbb Q}$ satisfying `IsDiamondAutHBar M H d σ`. Let $\mathcal O$ be a commutative ring which is a $\mathbb Z_p$-algebra, finite and free as a $\mathbb Z_p$-module. Write $\Gamma_H(M)\le \mathrm{SL}_2(\mathbb Z)$ for the image in $\mathrm{SL}_2(\mathbb Z)$ of the preimage of $H$ under `gamma0Units`, $V=\mathrm{Hom}(\Gamma_H(M)^{\mathrm{add}},\mathcal O)$ for the $\mathcal O$-module of additive characters of $\Gamma_H(M)$, and $V_{\mathrm{par}}\subseteq V$ for the submodule of those $\varphi$ vanishing on every $\gamma$ with $(\operatorname{tr}\gamma)^2=4$. Let $T=\operatorname{TateModule} p\,(J_H(M))$ be the module of sequences $(x_n)$ in $J_H(M)=\mathrm{Pic}^0$ of `xHFunctionFieldBar M H` with $p^nx_n=0$ and $px_{n+1}=x_n$. The assertion is that there is an $\mathcal O$-linear map $\Phi\colon V\to \mathrm{Hom}_{\mathcal O}(\mathcal O\otimes_{\mathbb Z_p}T,\mathcal O)$ such that: for every generator $g$ of [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) (a symbol $T_\ell$ for $\ell$ prime, $\ell\notin S$, $\ell\nmid M$, a symbol $U_q$ for $q$ prime dividing $M$, or a diamond symbol $\langle d\rangle$, $d\in(\mathbb Z/M)^\times$) and every $v\in V_{\mathrm{par}}$, one has $\Phi(\mathrm{opFamily}(g)\,v)=\Phi(v)\circ (\mathrm{tateGenOpH}(g)\otimes \mathcal O)$, where $\mathrm{opFamily}$ acts on $V$ by the transfer operators `heckeTL` for $T_\ell$ and $U_q$ and by `diamondL` for $\langle d\rangle$; $\Phi(V_{\mathrm{par}})$ is the whole dual; and $\Phi$ is injective on $V_{\mathrm{par}}$.
--
--   This is the comparison, with coefficients in a finite free $\mathbb Z_p$-algebra $\mathcal O$, between the parabolic cohomology of the modular curve $X_H(M)$ and the $\mathcal O$-dual of $\mathcal O\otimes_{\mathbb Z_p}T_pJ_H(M)$, compatible with the Hecke and diamond operators on both sides. Obtained from the $\mathbb Z_p$-coefficient statement [`ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH`](thm.html#ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH) by base change, it is the form used in the Taylor–Wiles argument, and is cited by [`CuspForm.TWLevel.exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH`](thm.html#CuspForm.TWLevel.exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_baseChange_tateModule_jH.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

theorem ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_baseChange_tateModule_jH
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (𝒪 : Type) [CommRing 𝒪] [Algebra ℤ_[p] 𝒪] [Module.Finite ℤ_[p] 𝒪] [Module.Free ℤ_[p] 𝒪] :
    ∃ Φ : CohCarrier.H1 M H 𝒪 →ₗ[𝒪]
        Module.Dual 𝒪 (𝒪 ⊗[ℤ_[p]] TateModule p (ModularCurve.JH M H)),
      (∀ (g : CohCarrier.Gen M S) (v : CohCarrier.H1 M H 𝒪),
        v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M H) 𝒪 →
          Φ (CohCarrier.opFamily M H S 𝒪 g v) =
            (Φ v) ∘ₗ (ModularCurve.tateGenOpH M H S p g).baseChange 𝒪) ∧
      (ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M H) 𝒪).map Φ = ⊤ ∧
      (∀ v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M H) 𝒪, Φ v = 0 → v = 0) := by sorry
