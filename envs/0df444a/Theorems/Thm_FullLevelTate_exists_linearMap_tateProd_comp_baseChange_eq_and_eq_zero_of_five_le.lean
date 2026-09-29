-- Prove2me | Theorems.Thm_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_five_le
-- name    : FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/9b032068-5a6d-514d-86fa-41d6cc5cbc5a
-- title:
--   Drinfeld specialisation of the full-level Tate module, q ≥ 5
-- statement:
--   Let $q \ge 5$ be a prime, $M' \ne 0$ a natural number with $q \nmid M'$, and $\lambda \ne q$ a prime. Assume [`ModularCurve.FullLevel.LevelAutInputs q M'`](def/ModularCurve_FullLevelJacobian.html#L220) (for each primitive $q$-th root of unity index $\zeta$ and each $\gamma \in \Gamma_0(M')$ there is an automorphism of the field `fieldBar q M'` over $\overline{\mathbb{Q}}$ acting on $q$-expansion quotients as $\gamma$ does) and [`ModularCurve.FullLevel.GL2Laws q M'`](def/ModularCurve_FullLevelJacobian.html#L255) (there is a monoid homomorphism $GL_2(\mathbb{Z}/q) \to \operatorname{End}(\mathrm{Jac}(q,M'))$ matching `slJac` on reductions of $\Gamma_0(M')$-matrices and `diagJac` on the matrices $\mathrm{diag}(1,d)$), where $\mathrm{Jac}(q,M') = \prod_{\zeta} J_H(q^2M')$; assume also that the Drinfeld coordinate ring of $q$ over $\overline{\mathbb{F}_{q^2}}$ is a domain. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $P$, let $\pi \in \overline{\mathbb{Q}}$ satisfy $\pi^{q^2-1} = q$, and let $\iota : \mathbb{F}_{q^2} \to \kappa(P)$ be a ring homomorphism. Then there exist a finite type $\mathrm{index}$ and a $\mathbb{Q}_\lambda$-linear map $sp_0$ from $\mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T_\lambda(\mathrm{Jac}(q,M'))$ to the product over $\mathrm{index}$ of copies of $\mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T_\lambda(\mathrm{Pic}^0)$ of the Drinfeld function field over $\overline{\mathbb{F}_{q^2}}$ such that: (A) for every $\tau$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$, every $\alpha \in \mathbb{F}_{q^2}^\times$ with $\iota(\alpha)$ equal to the tame value $P.\mathrm{tameCharacter}\,\pi\,\tau$ (the residue of $\tau(\pi)/\pi$ when that lies in $P$, and $0$ otherwise), and every $g \in GL_2(\mathbb{Z}/q)$ with $(g,\alpha)$ in the kernel `hSubgroup q` of $(g,\alpha) \mapsto \det(g)\,\alpha^{q+1}$, one has $sp_0 \circ (\mathrm{tateGL2}(g)\cdot\mathrm{tateGal}(\tau))_{\mathbb{Q}_\lambda} = \mathrm{tateProdRep}(\langle (g,\alpha)\rangle) \circ sp_0$; and (B) if $v$ satisfies $\sum_{t \in \mathbb{Z}/q} \mathrm{tateGL2}(u_t)\,\mathrm{tateGL2}(g)\,v = 0$ for all $g$, where $u_t = \begin{pmatrix}1&t\\0&1\end{pmatrix}$, and $sp_0 v = 0$, then $v = 0$.
--
--   This is the Drinfeld-curve specialisation of the rational $\lambda$-adic Tate module of the full-level-$q$ modular Jacobian over $\Gamma_0(M')$, in the branch $q \ge 5$: a tame-inertia-equivariant map into a finite product of Tate modules of the Jacobian of the Drinfeld curve, injective on vectors of cuspidal type. It is the coefficient-free core from which the coefficient-general form, `ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_comp_eq_zero_imp_of_levelAutInputs_of_five_le`, is obtained by base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_five_le.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_five_le
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
