-- Prove2me | Theorems.Thm_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_and_comp_eq_zero_imp_of_levelAutInputs_of_five_le
-- name    : FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_comp_eq_zero_imp_of_levelAutInputs_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/d7053947-2a70-577f-9418-a1c9a7e2a574
-- title:
--   Drinfeld-curve specialisation of the full-level Tate module, q≥ 5
-- statement:
--   Let $q\ge 5$ and $\lambda\ne q$ be primes, let $M'$ be a nonzero natural number not divisible by $q$, let $O'$ be a commutative $\mathbb{Z}_\lambda$-algebra, and write $T=\mathrm{TateModule}\,\lambda\,(\mathrm{Jac}\,q\,M')$ for the $\lambda$-adic Tate module of the full-level Jacobian $\mathrm{Jac}\,q\,M'=\mathrm{Idx}\,q\to J_H(q^2M',\,\mathrm{levelH}\,q\,M')$. Assume `LevelAutInputs q M'` (for every $\zeta\in\mathrm{Idx}\,q$ and every $\gamma\in\Gamma_0(M')$ there is an automorphism of `fieldBar q M'` over $\overline{\mathbb{Q}}$ satisfying `IsLevelAutBar`) and `GL2Laws q M'` (there is a monoid homomorphism $\mathrm{GL}_2(\mathbb{Z}/q)\to\mathrm{End}(\mathrm{Jac}\,q\,M')$ sending $\mathrm{redQ}\,\gamma$ to $\mathrm{slJac}\,\gamma$ for $\gamma\in\Gamma_0(M')$ and $\mathrm{diagOneElem}\,d$ to $\mathrm{diagJac}\,d$). Let $R$ be a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and $G$ one from $\mathrm{GL}_2(\mathbb{Z}/q)$ into $\mathrm{End}_{O'}(O'\otimes_{\mathbb{Z}_\lambda}T)$, acting on pure tensors as $a\otimes x\mapsto a\otimes \mathrm{tateGal}\,\sigma\,x$ and $a\otimes x\mapsto a\otimes\mathrm{tateGL2}\,g\,x$ respectively. Let $K$ be a field that is both an $O'$- and a $\mathbb{Q}_\lambda$-algebra, the two structure maps agreeing on $\mathbb{Z}_\lambda$. Assume the Drinfeld coordinate ring $\mathrm{CoordRing}\,q\,\overline{\mathbb{F}_{q^2}}$ is a domain. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $P$, let $\pi\in\overline{\mathbb{Q}}$ satisfy $\pi^{q^2-1}=q$, and let $\iota:\mathbb{F}_{q^2}\to$ the residue field of $P$ be a ring homomorphism. Then there are a finite type $\mathrm{index}$ and a $K$-linear map $$sp:K\otimes_{O'}(O'\otimes_{\mathbb{Z}_\lambda}T)\longrightarrow \mathrm{tateProd}\,q\,\overline{\mathbb{F}_{q^2}}\,\lambda\,K\,\mathrm{index},$$ the target being functions $\mathrm{index}\to K\otimes_{\mathbb{Q}_\lambda}$ (rational $\lambda$-adic Tate module of $\mathrm{Pic}^0$ of the Drinfeld function field), with two properties. First, for every $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$ (the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup inside the decomposition subgroup), every $\alpha\in\mathbb{F}_{q^2}^\times$ with $\iota(\alpha)=\mathrm{tameCharacter}\,P\,\pi\,\tau$, and every $g\in\mathrm{GL}_2(\mathbb{Z}/q)$ with $(g,\alpha)$ in the kernel $\mathrm{hSubgroup}\,q$ of $\mathrm{hChar}\,q$, one has $sp\circ (G g\cdot R\tau)\otimes K=\mathrm{tateProdRep}\,\langle(g,\alpha)\rangle\circ sp$. Second, for every monoid homomorphism $\theta:\mathbb{F}_{q^2}^\times\to K^\times$, every finite-dimensional $K$-representation $(W,\sigma)$ of $\mathrm{GL}_2(\mathbb{Z}/q)$ that is cuspidal of type $\theta$ in the sense of `IsCuspidalOfType`, and every $K$-linear $f:W\to K\otimes_{O'}(O'\otimes_{\mathbb{Z}_\lambda}T)$ intertwining $\sigma$ with the base change of $G$, the vanishing $sp\circ f=0$ forces $f=0$.
--
--   This is the branch $q\ge 5$ of the supercuspidal specialisation map from the full-level Tate module onto the Tate modules of Drinfeld curves in characteristic $q$, packaging the inertia- and $\mathrm{GL}_2(\mathbb{Z}/q)$-equivariance of the specialisation together with injectivity on cuspidal parts. It is invoked by the two general formulations [`FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_comp_eq_zero_imp_of_levelAutInputs`](thm.html#FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_comp_eq_zero_imp_of_levelAutInputs) and [`FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_comp_eq_zero_imp_of_levelAutInputs_of_ne_two_of_cast_eq_neg_one`](thm.html#FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_comp_eq_zero_imp_of_levelAutInputs_of_ne_two_of_cast_eq_neg_one), which treat the remaining small primes separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_and_comp_eq_zero_imp_of_levelAutInputs_of_five_le.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_comp_eq_zero_imp_of_levelAutInputs_of_five_le
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (lam : ℕ) [Fact lam.Prime] (hqlam : q ≠ lam)
    (O' : Type) [CommRing O'] [Algebra ℤ_[lam] O']
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (R : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')))
    (hR : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : O')
      (x : TateModule lam (ModularCurve.FullLevel.Jac q M')),
      R σ (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] ModularCurve.FullLevel.tateGal q M' lam σ x)
    (G : CuspidalType.GL2 q →* Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')))
    (hG : ∀ (g : CuspidalType.GL2 q) (a : O') (x : TateModule lam (ModularCurve.FullLevel.Jac q M')),
      G g (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] ModularCurve.FullLevel.tateGL2 q M' lam g x)
    (K : Type) [Field K] [Algebra O' K] [Algebra ℚ_[lam] K]
    (hOK : ∀ z : ℤ_[lam], algebraMap O' K (algebraMap ℤ_[lam] O' z) = algebraMap ℚ_[lam] K (z : ℚ_[lam]))
    [IsDomain (DrinfeldCurve.CoordRing q (AlgebraicClosure (GaloisField q 2)))]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P) :
    ∃ (index : Type) (_ : Finite index)
      (sp : K ⊗[O'] (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')) →ₗ[K]
        DrinfeldCurve.tateProd q (AlgebraicClosure (GaloisField q 2)) lam K index),
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
        ι (α : GaloisField q 2) = P.tameCharacter π τ →
          ∀ (g : CuspidalType.GL2 q) (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
            sp ∘ₗ ((G g * R τ).baseChange K) =
              DrinfeldCurve.tateProdRep q (AlgebraicClosure (GaloisField q 2)) lam K index ⟨(g, α), hg⟩ ∘ₗ sp) ∧
      (∀ (θ : (GaloisField q 2)ˣ →* Kˣ) {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
        (σ : Representation K (CuspidalType.GL2 q) W), CuspidalType.IsCuspidalOfType θ σ →
          ∀ f : W →ₗ[K] K ⊗[O'] (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')),
            (∀ x : CuspidalType.GL2 q, f ∘ₗ σ x = (G x).baseChange K ∘ₗ f) →
              sp ∘ₗ f = 0 → f = 0) := by sorry
