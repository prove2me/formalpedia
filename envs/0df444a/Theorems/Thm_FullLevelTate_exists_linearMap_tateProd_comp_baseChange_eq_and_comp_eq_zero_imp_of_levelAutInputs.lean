-- Prove2me | Theorems.Thm_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_and_comp_eq_zero_imp_of_levelAutInputs
-- name    : FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_comp_eq_zero_imp_of_levelAutInputs
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/f54c93ef-f4f3-54fb-8cbc-1112fce77241
-- title:
--   Drinfeld specialisation of the full level-q Tate module
-- statement:
--   Let $q$ and $\lambda$ be primes with $\lambda \neq q$, let $M' \geq 1$ with $q \nmid M'$, and let $O'$ be a commutative $\mathbb{Z}_\lambda$-algebra. Write $\mathrm{Jac}(q,M')$ for the product, indexed by [`ModularCurve.FullLevel.Idx q`](def/ModularCurve_FullLevelJacobian.html#L40), of copies of the Jacobian $J_H$ of level $q^2M'$ with $H \le (\mathbb{Z}/q^2M')^\times$ the kernel of reduction to $(\mathbb{Z}/q)^\times$, and $T_\lambda$ for the $\lambda$-adic Tate module of an abelian group, i.e. the group of sequences $(x_n)$ with $\lambda^n x_n = 0$ and $\lambda x_{n+1} = x_n$. Assume `LevelAutInputs q M'`: for each index $\zeta$ and each $\gamma \in \Gamma_0(M')$ there is an automorphism of the function field `fieldBar q M'` over $\overline{\mathbb{Q}}$ realising, on quotients of integral $q$-expansions, the weight-$k$ slash action by the conjugate of $\gamma$; and `GL2Laws q M'`: there is a monoid homomorphism from $\mathrm{GL}_2(\mathbb{Z}/q)$ to $\mathrm{End}(\mathrm{Jac}(q,M'))$ sending the reduction of each $\gamma \in \Gamma_0(M')$ to `slJac` and each $\mathrm{diag}(1,d)$ to `diagJac`. Let $R$ and $G$ be monoid homomorphisms from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, respectively $\mathrm{GL}_2(\mathbb{Z}/q)$, to $\mathrm{End}_{O'}(O' \otimes_{\mathbb{Z}_\lambda} T_\lambda \mathrm{Jac}(q,M'))$ acting on pure tensors through `tateGal`, respectively `tateGL2`. Let $K$ be a field that is an algebra over both $O'$ and $\mathbb{Q}_\lambda$, the two structure maps agreeing on $\mathbb{Z}_\lambda$; assume the coordinate ring [`DrinfeldCurve.CoordRing q`](def/DrinfeldCurve_CoordRing.html#L21) over $\overline{\mathbb{F}_{q^2}}$ is a domain. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ in its nonunits, $\pi \in \overline{\mathbb{Q}}$ with $\pi^{q^2-1} = q$, and $\iota$ a ring homomorphism from $\mathbb{F}_{q^2}$ to the residue field of $P$. Then there exist a finite type `index` and a $K$-linear map $sp$ from $K \otimes_{O'} (O' \otimes_{\mathbb{Z}_\lambda} T_\lambda \mathrm{Jac}(q,M'))$ to the `index`-indexed product of copies of $K \otimes_{\mathbb{Q}_\lambda} (\mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T_\lambda \mathrm{Pic}^0)$ of the Drinfeld curve over $\overline{\mathbb{F}_{q^2}}$ such that: (i) for every $\tau$ in the image of the inertia subgroup at $P$ and every $\alpha \in \mathbb{F}_{q^2}^\times$ with $\iota(\alpha)$ equal to the residue of $\tau(\pi)/\pi$, and every $g \in \mathrm{GL}_2(\mathbb{Z}/q)$ with $\det(g)\,\alpha^{q+1} = 1$, the map $sp$ intertwines the base change to $K$ of $G(g) \circ R(\tau)$ with the diagonal action of $(g,\alpha)$ through `tateProdRep`; and (ii) for every character $\theta : \mathbb{F}_{q^2}^\times \to K^\times$, every finite-dimensional $K$-representation $\sigma$ of $\mathrm{GL}_2(\mathbb{Z}/q)$ that is cuspidal of type $\theta$ (dimension $q-1$, no nonzero vector fixed by all upper unipotents, trivial on scalars, and the prescribed characteristic-polynomial identity on the nonsplit torus), and every $K$-linear $f$ from the representation space into $K \otimes_{O'} (O' \otimes_{\mathbb{Z}_\lambda} T_\lambda \mathrm{Jac}(q,M'))$ intertwining $\sigma$ with the base change of $G$, the vanishing $sp \circ f = 0$ forces $f = 0$.
--
--   This is the specialisation step that compares the $\lambda$-adic Tate module of the full level-$q$ modular Jacobian with Tate modules of Drinfeld's curve in characteristic $q$, equivariantly for the tame inertia labels at a place above $q$, and records that the specialisation is faithful on cuspidal-type intertwiners. It feeds the construction of the eigenspace data used in the level-lowering argument at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_and_comp_eq_zero_imp_of_levelAutInputs.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_comp_eq_zero_imp_of_levelAutInputs
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
