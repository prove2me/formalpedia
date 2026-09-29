-- Prove2me | Theorems.Thm_FullLevelTate_comp_baseChange_mul_eq_tateProdRep_comp_of_det_eq_one_of_diagOneElem
-- name    : FullLevelTate.comp_baseChange_mul_eq_tateProdRep_comp_of_det_eq_one_of_diagOneElem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/3d21b1be-9793-5121-a29c-df2c84467859
-- title:
--   Equivariance of the Drinfeld specialisation from two generating cases
-- statement:
--   Fix primes $q$ and $\lambda$ and a natural number $M' \neq 0$, and assume the predicate [`ModularCurve.FullLevel.GL2Laws q M'`](def/ModularCurve_FullLevelJacobian.html#L255), i.e. that there is a monoid homomorphism from $GL_2(\mathbb{Z}/q)$ to the additive endomorphisms of the full-level Jacobian [`ModularCurve.FullLevel.Jac q M'`](def/ModularCurve_FullLevelJacobian.html#L85) which agrees with the $SL_2(\mathbb{Z})$-action on $\Gamma_0(M')$ and with the diamond-type operators on the matrices $\mathrm{diag}(1,d)$. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$, let $\pi \in \overline{\mathbb{Q}}$, let $\iota : \mathbb{F}_{q^2} \to \kappa(P)$ be a ring homomorphism into the residue field of $P$, let $k$ be a field equipped with an $\mathbb{F}_{q^2}$-algebra structure such that the Drinfeld coordinate ring [`DrinfeldCurve.CoordRing q k`](def/DrinfeldCurve_CoordRing.html#L21) is a domain, let $I$ be a type, and let $sp$ be a $\mathbb{Q}_\lambda$-linear map from the rational Tate module $\mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T_\lambda(\mathrm{Jac}(q;M'))$ to [`DrinfeldCurve.tateProd q k lam ℚ_[lam] I`](def/DrinfeldCurve_TateRep.html#L27), the $I$-indexed product of copies of $\mathbb{Q}_\lambda \otimes_{\mathbb{Q}_\lambda}$ the rational Tate module of $\mathrm{Pic}^0$ of the Drinfeld function field over $k$. Assume: (level) for every $h$ in the subgroup [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276) of $GL_2(\mathbb{Z}/q) \times \mathbb{F}_{q^2}^\times$ whose second component is $1$, the base change to $\mathbb{Q}_\lambda$ of the operator attached by `tateGL2` to the first component of $h$ intertwines $sp$ with `tateProdRep` at $h$; (inertia) for every $\tau$ in the image `P.inertiaSubgroupIn ℚ` of the inertia subgroup of $P$ inside $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and every $h$ in `hSubgroup q` whose second component has $\iota$-image equal to the tame character $\tau \pi/\pi$ of $\tau$ at $\pi$ and whose first component is of the form $\mathrm{diag}(1,e)$ for some $e \in (\mathbb{Z}/q)^\times$, the base change of the product of the `tateGL2` operator of that first component with the `tateGal` operator of $\tau$ intertwines $sp$ with `tateProdRep` at $h$. The conclusion is that the same intertwining holds for arbitrary $g$: for every such $\tau$, every $\alpha \in \mathbb{F}_{q^2}^\times$ with $\iota(\alpha)$ the tame character of $\tau$ at $\pi$, and every $g \in GL_2(\mathbb{Z}/q)$ with $(g,\alpha) \in$ `hSubgroup q`, one has $sp \circ (\mathrm{tateGL2}(g)\,\mathrm{tateGal}(\tau))_{\mathbb{Q}_\lambda} = \mathrm{tateProdRep}(g,\alpha) \circ sp$.
--
--   This is the group-theoretic assembly step for the equivariance of a specialisation map from the full-level modular Tate module to the Tate module of the Drinfeld curve: it upgrades equivariance known on the two generating families (elements pairing with $\alpha = 1$, and the diagonal matrices $\mathrm{diag}(1,e)$ twisted by an inertia element) to all admissible pairs. It is used in the constructions of such specialisation maps attached to semistable coverings and models with prescribed reduction and inertia behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FullLevelTate_comp_baseChange_mul_eq_tateProdRep_comp_of_det_eq_one_of_diagOneElem.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem FullLevelTate.comp_baseChange_mul_eq_tateProdRep_comp_of_det_eq_one_of_diagOneElem
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (lam : ℕ) [Fact lam.Prime]
    (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ)
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)]
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P)
    (I : Type)
    (sp : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') →ₗ[ℚ_[lam]]
      DrinfeldCurve.tateProd q k lam ℚ_[lam] I)
    (hlevel : ∀ h : DrinfeldCurve.hSubgroup q,
      ((h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 = 1) →
        sp ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam
            (h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1).baseChange ℚ_[lam] =
          DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I h ∘ₗ sp)
    (hinert : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ h : DrinfeldCurve.hSubgroup q,
      ι ((h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2 : GaloisField q 2) =
          P.tameCharacter π τ →
        (∃ e : (ZMod q)ˣ, (h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 =
          ModularCurve.FullLevel.diagOneElem q e) →
        sp ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam
              (h : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 *
            ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] =
          DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I h ∘ₗ sp) :
    ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
      ι (α : GaloisField q 2) = P.tameCharacter π τ →
        ∀ (g : CuspidalType.GL2 q) (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
          sp ∘ₗ (ModularCurve.FullLevel.tateGL2 q M' lam g *
              ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] =
            DrinfeldCurve.tateProdRep q k lam ℚ_[lam] I ⟨(g, α), hg⟩ ∘ₗ sp := by sorry
