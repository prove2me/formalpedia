-- Prove2me | Theorems.Thm_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH
-- name    : ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/c4e0a67d-bb0a-5f90-b5ca-da3974fcc335
-- title:
--   Parabolic cohomology of Γ_H(M) versus dual Tate module of J_H
-- statement:
--   Fix an integer $M \neq 0$, a prime $p$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$ and a set $S$ of natural numbers, and let $\Gamma_H(M) = \mathtt{GammaH}\,M\,H$ be the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained from the preimage of $H$ under the homomorphism `gamma0Units` sending $\gamma \in \Gamma_0(M)$ to the class of its lower right entry in $(\mathbb{Z}/M)^{\times}$. Assume `HeckeDiamondInputsHAll M H`: for every prime $\ell$ the predicate `HeckeInputsHAlong` holds for $(\mathbb{Z}/M)$-data $M, H, \ell$ over $\overline{\mathbb{Q}}$, and for every $d \in (\mathbb{Z}/M)^{\times}$ there is an automorphism $\sigma$ of the geometric function field `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ satisfying `IsDiamondAutHBar M H d σ`. The assertion is that there exists a $\mathbb{Z}_p$-linear map $\Phi$ from $H^1 = (\mathrm{Additive}\,\Gamma_H(M) \to_{+} \mathbb{Z}_p)$, the module of additive homomorphisms from the abelianised group to $\mathbb{Z}_p$, to the $\mathbb{Z}_p$-dual of the Tate module $T_p J_H(M)$, the module of sequences $(x_n)$ in $J_H(M) = \mathrm{Pic}^0$ of `xHFunctionFieldBar M H` with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, such that: first, for each formal generator $g$ of `Gen M S` (a $T_\ell$ for $\ell$ prime, $\ell \notin S$, $\ell \nmid M$; a $U_q$ for $q$ prime dividing $M$; or a diamond $\langle d \rangle$) and each $v$ in the submodule `parabolicHoms` of homomorphisms vanishing on every $\gamma \in \Gamma_H(M)$ with $(\operatorname{tr}\gamma)^2 = 4$, one has $\Phi(\mathtt{opFamily}\,g\,v) = \Phi(v) \circ \mathtt{tateGenOpH}\,g$, where `opFamily` is the cohomological operator (`heckeTL` at $\ell$ or $q$, `diamondL` at $d$) and `tateGenOpH` is the endomorphism of $T_p J_H(M)$ induced by $g$; secondly, $\Phi$ maps the parabolic submodule onto the whole dual; and thirdly, $\Phi$ is injective on the parabolic submodule.
--
--   This is the Eichler–Shimura style comparison underlying the construction of the $p$-adic Galois representations attached to modular forms: parabolic group cohomology of $\Gamma_H(M)$ with $\mathbb{Z}_p$-coefficients is identified, compatibly with the Hecke and diamond operators, with the $\mathbb{Z}_p$-dual of the $p$-adic Tate module of the Jacobian $J_H(M)$. It is used to transport Hecke-module structure to the Tate module, and is cited in the construction of the Galois representation on parabolic cohomology, in its base-changed variant, and in the proof that the rational Tate module of $J_H(M)$ is two-dimensional over the relevant Hecke field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) :
    ∃ Φ : CohCarrier.H1 M H ℤ_[p] →ₗ[ℤ_[p]]
        (TateModule p (ModularCurve.JH M H) →ₗ[ℤ_[p]] ℤ_[p]),
      (∀ (g : CohCarrier.Gen M S) (v : CohCarrier.H1 M H ℤ_[p]),
        v ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p] →
          Φ (CohCarrier.opFamily M H S ℤ_[p] g v) = (Φ v) ∘ₗ ModularCurve.tateGenOpH M H S p g) ∧
      (ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p]).map Φ = ⊤ ∧
      (∀ v ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p], Φ v = 0 → v = 0) := by sorry
