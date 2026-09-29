-- Prove2me | Theorems.Thm_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_two_of_dvd
-- name    : FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_two_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/c7b3378a-747c-54cf-bb58-21401fcbdadd
-- title:
--   Drinfeld specialisation of the full-level-2 Tate module
-- statement:
--   Fix a prime $q$ with $q=2$, a nonzero natural number $M'$ not divisible by $q$, a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$, and a prime $\lambda \neq q$. Assume [`ModularCurve.FullLevel.LevelAutInputs q M'`](def/ModularCurve_FullLevelJacobian.html#L220) (for every index $\zeta$ and every $\gamma \in \Gamma_0(M')$ there is an $\overline{\mathbb{Q}}$-automorphism of the field `fieldBar q M'` realising the action of $\gamma$ on $q$-expansions in the sense of `IsLevelAutBar`) and [`ModularCurve.FullLevel.GL2Laws q M'`](def/ModularCurve_FullLevelJacobian.html#L255) (there is a monoid homomorphism from $GL_2(\mathbb{Z}/q)$ to the additive endomorphisms of $\mathrm{Jac}\,(q,M') = \mathrm{Idx}(q) \to J_H(q^2M')$ sending reductions of $\Gamma_0(M')$-matrices to `slJac` and the matrices $\mathrm{diag}(1,d)$ to `diagJac`), together with the assumption that the Drinfeld coordinate ring over $\overline{\mathbb{F}_{q^2}}$ is a domain. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $P$, let $\pi \in \overline{\mathbb{Q}}$ satisfy $\pi^{q^2-1} = q$, and let $\iota : \mathbb{F}_{q^2} \to \kappa(P)$ be a ring homomorphism. Then there exist a finite type $\mathrm{index}$ and a $\mathbb{Q}_\lambda$-linear map $sp_0$ from $V_\lambda = \mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T_\lambda(\mathrm{Jac}\,(q,M'))$ to the product, over $\mathrm{index}$, of $\mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T_\lambda \mathrm{Pic}^0$ of the Drinfeld function field over $\overline{\mathbb{F}_{q^2}}$, with the following two properties. First, equivariance: for every $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$ (the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup inside the decomposition subgroup), every $\alpha \in \mathbb{F}_{q^2}^\times$ with $\iota(\alpha)$ equal to the tame character value $P.\mathrm{tameCharacter}\,\pi\,\tau$ (the residue of $\tau(\pi)/\pi$ when this lies in $P$, and $0$ otherwise), and every $g \in GL_2(\mathbb{Z}/q)$ with $(g,\alpha)$ in the kernel `hSubgroup q` of the character $(g,\alpha) \mapsto \det(g)\,\alpha^{q+1}$, the composite of the base change to $\mathbb{Q}_\lambda$ of `tateGL2 q M' lam g * tateGal q M' lam τ` followed by $sp_0$ equals $sp_0$ followed by `tateProdRep` at $\langle (g,\alpha), hg\rangle$. Second, a kernel statement: any $v \in V_\lambda$ with $sp_0 v = 0$ such that, for every $g \in GL_2(\mathbb{Z}/q)$, the operator $\sum_{t \in \mathbb{Z}/q} \mathrm{tateGL2}(u(t)) \cdot \mathrm{tateGL2}(g)$ (base changed to $\mathbb{Q}_\lambda$, with $u(t)$ the upper unipotent matrix with entry $t$) kills $v$, is itself zero.
--
--   This is the coefficient-free form, at the auxiliary level $\Gamma_0(M')$ with $\ell \equiv 11 \pmod{12}$ dividing $M'$, of the specialisation of the rational $\lambda$-adic Tate module of the full-level-$q$ modular Jacobian onto the Tate modules of $\mathrm{Pic}^0$ of the Drinfeld curve in characteristic $q = 2$, the map being equivariant for the combined $GL_2(\mathbb{Z}/q)$ and inertia action via the subgroup $\mathrm{hSubgroup}$, and injective on vectors annihilated by all unipotent sums (the non-cuspidal part). It feeds the version [`FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_two`](thm.html#FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_two), where the divisibility hypothesis on $M'$ by such an $\ell$ is removed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_two_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_two_of_dvd
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (lam : ℕ) [Fact lam.Prime] (hqlam : q ≠ lam)
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hGL : ModularCurve.FullLevel.GL2Laws q M')
    [IsDomain (DrinfeldCurve.CoordRing q (AlgebraicClosure (GaloisField q 2)))]
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P) :
    ∃ (index : Type) (_ : Finite index)
      (sp₀ : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') →ₗ[ℚ_[lam]]
        DrinfeldCurve.tateProd q (AlgebraicClosure (GaloisField q 2)) lam ℚ_[lam] index),
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
        ι (α : GaloisField q 2) = P.tameCharacter π τ →
          ∀ (g : CuspidalType.GL2 q) (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
            sp₀ ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam g *
                ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] =
              DrinfeldCurve.tateProdRep q (AlgebraicClosure (GaloisField q 2)) lam ℚ_[lam] index ⟨(g, α), hg⟩ ∘ₗ
                sp₀) ∧
      (∀ v : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M'),
        (∀ g : CuspidalType.GL2 q,
          (∑ t : ZMod q,
            (ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam] *
              (ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam]) v = 0) →
        sp₀ v = 0 → v = 0) := by sorry
