-- Prove2me | Theorems.Thm_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution
-- name    : ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/ed446054-3799-52bb-ba1f-7c909058b414
-- title:
--   Hecke-equivariant map from parabolic cohomology to the dual Tate module
-- statement:
--   Let $M$ be a nonzero natural number, $p$ a prime, $H$ a subgroup of $(\mathbb{Z}/M)^\times$ and $S$ a set of natural numbers, and assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113): for every prime $\ell$ the Hecke data `HeckeInputsHAlong` over $\overline{\mathbb{Q}}$ for $M$, $H$, $\ell$ hold, and every $d \in (\mathbb{Z}/M)^\times$ is realised by some $\overline{\mathbb{Q}}$-automorphism $\sigma$ of the function field `xHFunctionFieldBar M H` satisfying `IsDiamondAutHBar M H d σ`. Then there is a $\mathbb{Z}_p$-linear map $\Phi$ from $H^1(M,H;\mathbb{Z}_p)$, the additive homomorphisms $\mathrm{Additive}(\Gamma_H(M)) \to \mathbb{Z}_p$ where $\Gamma_H(M)$ is the preimage in $\Gamma_0(M)$ of $H$ under the lower-right-entry character, to the $\mathbb{Z}_p$-dual of the Tate module $\mathrm{Ta}_p(J_H(M))$ — the sequences $(x_n)$ in the degree-zero divisor class group $\mathrm{Pic}^0$ of `xHFunctionFieldBar M H` with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$ — with four properties. First, for every generator $g$ in [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) (a prime $\ell \notin S$ with $\ell \nmid M$, a prime $q \mid M$, or $d \in (\mathbb{Z}/M)^\times$) and every $v$ in the submodule `parabolicHoms` of homomorphisms vanishing on the parabolic elements of $\Gamma_H(M)$, $\Phi$ of the operator `opFamily M H S ℤ_[p] g` applied to $v$ equals $\Phi(v)$ precomposed with the operator `tateGenOpH M H S p g` on the Tate module. Second, for parabolic $v$, $\Phi$ of `charInvolution` applied to $v$ (precomposition of $v$ with the involution `jConjGammaH` of $\Gamma_H(M)$) equals $\Phi(v)$ precomposed with the Tate-module action of [`complexConjugation`](def/GaloisRep_ComplexConjugation.html#L30). Third, $\Phi$ maps the parabolic submodule onto the whole dual, and fourth, $\Phi$ is injective on that submodule.
--
--   This is the Eichler–Shimura style comparison between the parabolic group cohomology of $\Gamma_H(M)$ with $\mathbb{Z}_p$-coefficients and the $\mathbb{Z}_p$-dual of the $p$-adic Tate module of the Jacobian $J_H(M)$, in a form that matches the Hecke and diamond operators on the two sides and matches the involution induced by $j$-conjugation with the action of complex conjugation. It feeds [`CohCarrier.exists_galoisModule_parabolicHoms_to_dual_charInvolution_frobenius`](thm.html#CohCarrier.exists_galoisModule_parabolicHoms_to_dual_charInvolution_frobenius), which transports the Galois module structure on the Tate module, together with the behaviour of Frobenius elements, onto parabolic cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CohCarrier_CharInvolution
import Definitions.Def_GaloisRep_ComplexConjugation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) :
    ∃ Φ : CohCarrier.H1 M H ℤ_[p] →ₗ[ℤ_[p]]
        (TateModule p (ModularCurve.JH M H) →ₗ[ℤ_[p]] ℤ_[p]),
      (∀ (g : CohCarrier.Gen M S) (v : CohCarrier.H1 M H ℤ_[p]),
        v ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p] →
          Φ (CohCarrier.opFamily M H S ℤ_[p] g v) = (Φ v) ∘ₗ ModularCurve.tateGenOpH M H S p g) ∧
      (∀ v ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p],
        Φ (CohCarrier.charInvolution M H ℤ_[p] ℤ_[p] v) =
          (Φ v) ∘ₗ ModularCurve.JH.tateGaloisRep M H p complexConjugation) ∧
      (ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p]).map Φ = ⊤ ∧
      (∀ v ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p], Φ v = 0 → v = 0) := by sorry
