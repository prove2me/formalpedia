-- Prove2me | Theorems.Thm_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_two
-- name    : FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/9a723d19-7b4d-5a41-8fb5-bb003b1c45b0
-- title:
--   Drinfeld-curve specialisation at q=2 of the full-level Tate module
-- statement:
--   Let $q$ be a prime with $q=2$, let $M'\ge 1$ be an integer not divisible by $q$, and let $\lambda$ be a prime with $q\neq\lambda$. Assume the level-automorphism input [`ModularCurve.FullLevel.LevelAutInputs q M'`](def/ModularCurve_FullLevelJacobian.html#L220) (for every $q$-th root-of-unity index $\zeta$ and every $\gamma\in\Gamma_0(M')$ there is an automorphism of the relevant function field over $\overline{\mathbb Q}$ satisfying the $q$-expansion identity `IsLevelAutBar`) and the input [`ModularCurve.FullLevel.GL2Laws q M'`](def/ModularCurve_FullLevelJacobian.html#L255) (existence of an action $G$ of $\mathrm{GL}_2(\mathbb Z/q)$ on $\mathrm{Jac}(q,M')$ with $G(\bar\gamma)=$ `slJac` $\gamma$ for $\gamma\in\Gamma_0(M')$ and $G$ of $\mathrm{diag}(1,d)=$ `diagJac` $d$), together with the assumption that the Drinfeld coordinate ring over $\overline{\mathbb F_{q^2}}$ is a domain. Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $P$, let $\pi\in\overline{\mathbb Q}$ satisfy $\pi^{q^2-1}=q$, and let $\iota:\mathbb F_{q^2}\to\kappa(P)$ be a ring homomorphism. Then there are a finite type `index` and a $\mathbb Q_\lambda$-linear map $sp_0$ from $\mathbb Q_\lambda\otimes_{\mathbb Z_\lambda}T_\lambda(\mathrm{Jac}(q,M'))$ to the product over `index` of $\mathbb Q_\lambda\otimes\bigl(\mathbb Q_\lambda\otimes_{\mathbb Z_\lambda}T_\lambda(\mathrm{Pic}^0)\bigr)$ of the Drinfeld function field over $\overline{\mathbb F_{q^2}}$, such that: (A) for every $\tau$ in the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$, every $\alpha\in\mathbb F_{q^2}^\times$ with $\iota(\alpha)$ equal to the tame value $\mathrm{res}_P(\tau\pi/\pi)$, and every $g\in\mathrm{GL}_2(\mathbb Z/q)$ with $(g,\alpha)$ in the kernel of $(g,\alpha)\mapsto\det(g)\,\alpha^{q+1}$, the base change to $\mathbb Q_\lambda$ of `tateGL2` $g\cdot$ `tateGal` $\tau$ followed by $sp_0$ equals $sp_0$ followed by the diagonal action `tateProdRep` of $(g,\alpha)$; and (B) every $v$ with $sp_0v=0$ which satisfies, for all $g\in\mathrm{GL}_2(\mathbb Z/q)$, $\bigl(\sum_{t\in\mathbb Z/q}\,$`tateGL2`$(\text{unipotent }t)\circ$`tateGL2`$(g)\bigr)v=0$ after base change, is zero.
--
--   This is the coefficient-free specialisation statement at the small prime $q=2$: the rational $\lambda$-adic Tate module of the Jacobian of the full level-$q$ modular curve over $\Gamma_0(M')$ maps to a finite product of rational Tate modules of the Drinfeld curve $xy^q-x^qy=1$ over $\overline{\mathbb F_{q^2}}$, equivariantly for the combined $\mathrm{GL}_2(\mathbb F_q)$-and-inertia action through the tame character, and injectively on the cuspidal part. It supplies the $q=2$ case of [`FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_comp_eq_zero_imp_of_levelAutInputs_of_eq_two`](thm.html#FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_comp_eq_zero_imp_of_levelAutInputs_of_eq_two), the auxiliary level $M''=\ell M'$ with $\ell\equiv 11\pmod{12}$ being introduced by the companion result for levels divisible by such an $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FullLevelTate_exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem FullLevelTate.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
