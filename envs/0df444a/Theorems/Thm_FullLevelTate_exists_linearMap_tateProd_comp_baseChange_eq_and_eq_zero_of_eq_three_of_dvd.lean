-- Prove2me | Theorems.Thm_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_three_of_dvd
-- name    : FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/1cee085f-8415-5842-b80a-dad5ea64722a
-- title:
--   Drinfeld specialisation of the full-level-3 Tate module, q=3
-- statement:
--   Fix a prime $q$ with $q = 3$, a nonzero natural number $M'$ not divisible by $q$, a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$, and a prime $\lambda \neq q$. Assume [`ModularCurve.FullLevel.LevelAutInputs q M'`](def/ModularCurve_FullLevelJacobian.html#L220), i.e. for every $\zeta$ in `Idx q` and every $\gamma \in \Gamma_0(M')$ in $SL(2,\mathbb{Z})$ there is an automorphism of the field `fieldBar q M'` over $\overline{\mathbb{Q}}$ satisfying the $q$-expansion identity `IsLevelAutBar`; assume [`ModularCurve.FullLevel.GL2Laws q M'`](def/ModularCurve_FullLevelJacobian.html#L255), i.e. there is a monoid homomorphism $G : GL_2(\mathbb{Z}/q) \to \mathrm{End}(\mathrm{Jac}(q,M'))$ with $G(\bar\gamma) =$ `slJac` $\gamma$ for $\gamma \in \Gamma_0(M')$ and $G($`diagOneElem` $d) =$ `diagJac` $d$ for $d \in (\mathbb{Z}/q)^\times$; and assume the Drinfeld coordinate ring of $q$ over $\overline{\mathbb{F}_{q^2}}$ is a domain. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $P$, let $\pi \in \overline{\mathbb{Q}}$ satisfy $\pi^{q^2-1} = q$, and let $\iota : \mathbb{F}_{q^2} \to \kappa(P)$ be a ring homomorphism. Then there exist a finite type `index` and a $\mathbb{Q}_\lambda$-linear map $sp_0$ from $\mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T_\lambda(\mathrm{Jac}(q,M'))$, where $\mathrm{Jac}(q,M') =$ `Idx q` $\to J_H(q^2M')$, to the product over `index` of $\mathbb{Q}_\lambda \otimes_{\mathbb{Q}_\lambda}$ the rational Tate module of $\mathrm{Pic}^0$ of the Drinfeld function field of $q$ over $\overline{\mathbb{F}_{q^2}}$, such that: (i) for every $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$, every $\alpha \in \mathbb{F}_{q^2}^\times$ with $\iota(\alpha)$ equal to the tame character value $P.\mathrm{tameCharacter}\,\pi\,\tau$ (the residue of $\tau\pi/\pi$ when this lies in $P$, and $0$ otherwise), and every $g \in GL_2(\mathbb{Z}/q)$ with $(g,\alpha)$ in the kernel `hSubgroup q` of the character $(g,\alpha) \mapsto \det(g)\,\alpha^{q+1}$, one has $sp_0$ precomposed with the base change to $\mathbb{Q}_\lambda$ of `tateGL2 g * tateGal τ` equal to `tateProdRep` at $\langle (g,\alpha), hg\rangle$ composed with $sp_0$; and (ii) every $v$ in the rational Tate module which is annihilated by all the operators $\sum_{t \in \mathbb{Z}/q}$ `tateGL2 (unipotent t)` $\cdot$ `tateGL2 g` (base changed to $\mathbb{Q}_\lambda$), $g \in GL_2(\mathbb{Z}/q)$, and satisfies $sp_0 v = 0$, is zero.
--
--   This is the case $q = 3$ of the specialisation of the $\lambda$-adic Tate module of the full-level-$q$ modular Jacobian onto Tate modules of the Drinfeld curve attached to $GL_2(\mathbb{F}_q)$, equivariant for the inertia action paired with the $GL_2(\mathbb{F}_q)$-action through the character $\det(g)\alpha^{q+1}$, and injective on vectors not killed by the unipotent trace operators. It is stated with the Drinfeld side taken over the algebraic closure of $\mathbb{F}_{q^2}$ rather than over the residue field of $P$, and is used in the corresponding statement with the divisibility hypothesis on $M'$ removed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_three_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_three_of_dvd
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
