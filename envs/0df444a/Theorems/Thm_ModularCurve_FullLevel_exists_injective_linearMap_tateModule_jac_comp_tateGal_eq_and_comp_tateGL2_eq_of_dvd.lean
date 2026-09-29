-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_injective_linearMap_tateModule_jac_comp_tateGal_eq_and_comp_tateGL2_eq_of_dvd
-- name    : ModularCurve.FullLevel.exists_injective_linearMap_tateModule_jac_comp_tateGal_eq_and_comp_tateGL2_eq_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/2a128d4c-0cb1-53b8-a9e2-bca2a5be7abb
-- title:
--   Equivariant injection of λ-adic Tate modules for M' ∣ M''
-- statement:
--   Let $q$ be a prime, let $M'$ and $M''$ be nonzero natural numbers with $M' \mid M''$ and $q \nmid M''$, and let $\lambda$ be a prime. Assume at both levels the two input predicates: `LevelAutInputs q M'` and `LevelAutInputs q M''`, i.e. for every index $\zeta$ in `Idx q` and every $\gamma \in SL(2,\mathbb{Z})$ lying in $\Gamma_0$ of the respective level there is an automorphism $\tau$ of the geometric function field `fieldBar` over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ realising, on quotients of integral $q$-expansions of modular forms for $\Gamma_H(q^2 M)$, the slash action by `conjElem q γ` after any embedding of the algebraic closure into $\mathbb{C}$ carrying $\zeta$ to $e^{2\pi i/q}$; and `GL2Laws q M'`, `GL2Laws q M''`, i.e. there is a monoid homomorphism from $GL_2(\mathbb{Z}/q)$ to the additive endomorphisms of $\mathrm{Jac}$ sending the reduction of $\gamma \in \Gamma_0$ of the level to `slJac` of $\gamma$ and the matrix $\mathrm{diag}(1,d)$ to `diagJac` of $d$, for every unit $d$ of $\mathbb{Z}/q$. Then there exists a $\mathbb{Z}_\lambda$-linear map $\delta$ from the $\lambda$-adic Tate module of $\mathrm{Jac}(q,M')$ — the group of sequences $(x_n)$ in the Jacobian with $\lambda^n x_n = 0$ and $\lambda x_{n+1} = x_n$ — to that of $\mathrm{Jac}(q,M'')$ such that $\delta$ is injective, $\delta \circ \mathrm{tateGal}_{M'}(\sigma) = \mathrm{tateGal}_{M''}(\sigma) \circ \delta$ for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, and $\delta \circ \mathrm{tateGL2}_{M'}(g) = \mathrm{tateGL2}_{M''}(g) \circ \delta$ for every $g \in GL_2(\mathbb{Z}/q)$. Here $\mathrm{Jac}(q,M)$ is the product over `Idx q` of the Jacobians $J_H(q^2 M)$, carrying the coefficientwise Galois action `galJac` and the $GL_2(\mathbb{Z}/q)$-action `gl2Jac`.
--
--   This is the degeneracy (conorm, or Picard pull-back) comparison between the full-level modular Jacobians at levels $M' \mid M''$, realised on $\lambda$-adic Tate modules and compatible with both the Galois and the $GL_2(\mathbb{F}_q)$-actions. It is used by the statements producing maps between products of Tate modules at the primes $\lambda = 3$ and $\lambda = 2$, which feed the comparison of the Frey curve's representation with the modular one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_injective_linearMap_tateModule_jac_comp_tateGal_eq_and_comp_tateGL2_eq_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.FullLevel.exists_injective_linearMap_tateModule_jac_comp_tateGal_eq_and_comp_tateGL2_eq_of_dvd
    (q : ℕ) [Fact q.Prime] (M' M'' : ℕ) [NeZero M'] [NeZero M''] (hM : M' ∣ M'') (hqM'' : ¬ q ∣ M'')
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (hLA'' : ModularCurve.FullLevel.LevelAutInputs q M'') (hGL'' : ModularCurve.FullLevel.GL2Laws q M'')
    (lam : ℕ) [Fact lam.Prime] :
    ∃ δ : TateModule lam (ModularCurve.FullLevel.Jac q M') →ₗ[ℤ_[lam]]
        TateModule lam (ModularCurve.FullLevel.Jac q M''),
      Function.Injective δ ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        δ ∘ₗ ModularCurve.FullLevel.tateGal q M' lam σ = ModularCurve.FullLevel.tateGal q M'' lam σ ∘ₗ δ) ∧
      (∀ g : CuspidalType.GL2 q,
        δ ∘ₗ ModularCurve.FullLevel.tateGL2 q M' lam g = ModularCurve.FullLevel.tateGL2 q M'' lam g ∘ₗ δ) := by sorry
