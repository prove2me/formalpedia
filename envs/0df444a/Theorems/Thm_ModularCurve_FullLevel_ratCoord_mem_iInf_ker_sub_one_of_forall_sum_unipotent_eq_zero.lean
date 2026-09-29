-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_ratCoord_mem_iInf_ker_sub_one_of_forall_sum_unipotent_eq_zero
-- name    : ModularCurve.FullLevel.ratCoord_mem_iInf_ker_sub_one_of_forall_sum_unipotent_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/d9a1468d-e765-58b2-840f-f19fa68d7871
-- title:
--   Cuspidal vectors have tame-inertia-invariant components at full level
-- statement:
--   Let $q$ and $\lambda$ be primes with $q \neq \lambda$ and let $M' \geq 1$ with $q \nmid M'$. Write $\mathrm{Idx}\,q$ for the set of primitive $q$-th roots of unity in $\overline{\mathbb{Q}}$, let $H \leq (\mathbb{Z}/q^2M')^\times$ be the kernel of reduction to $(\mathbb{Z}/q)^\times$ (the units $\equiv 1 \bmod q$), let `fieldBar q M'` be the $\overline{\mathbb{Q}}$-function field obtained by base change from the $q$-expansion function field of $X_H$ of level $q^2M'$, let `jacComp q M'` $= J_H$ be its degree-zero divisor class group $\mathrm{Pic}^0$, and let `Jac q M'` be the group of functions $\mathrm{Idx}\,q \to J_H$. Assume `LevelAutInputs q M'` (for every $\zeta$ and every $\gamma \in SL_2(\mathbb{Z})$ lying in $\Gamma_0(M')$ there is an automorphism of `fieldBar q M'` over $\overline{\mathbb{Q}}$ satisfying the $q$-expansion identity `IsLevelAutBar q M' ζ γ`) and `GL2Laws q M'` (there is a monoid homomorphism $GL_2(\mathbb{F}_q) \to \mathrm{End}(\mathrm{Jac}\,q\,M')$ carrying the reduction of $\gamma \in \Gamma_0(M')$ to `slJac q M' γ` and $\mathrm{diag}(1,d)$ to `diagJac q M' d`); the induced $\mathbb{Z}_\lambda$-linear actions on $T_\lambda(\mathrm{Jac}\,q\,M')$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, of $GL_2(\mathbb{F}_q)$ and of additive endomorphisms are `tateGal`, `tateGL2` and `tateEnd`. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $P$, and $\pi \in P$ with $\pi^{q^2-1} = q$. Assume the span hypothesis: for every $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$ whose tame character $P.\mathrm{tameCharacter}\,\pi\,\tau$ (the residue of $\tau\pi/\pi$) equals $1$, the image of $\tau - 1$ on $V = \mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T_\lambda(\mathrm{Jac}\,q\,M')$ lies in the $\mathbb{Q}_\lambda$-span of the vectors $g\cdot w$ with $g \in GL_2(\mathbb{F}_q)$ and $w \in V$ fixed by all unipotents $\begin{pmatrix}1&t\\0&1\end{pmatrix}$, $t \in \mathbb{Z}/q$. Let $\Psi$ be a $\mathbb{Z}_\lambda$-linear isomorphism $T_\lambda(\mathrm{Jac}\,q\,M') \cong \prod_{\zeta \in \mathrm{Idx}\,q} T_\lambda(J_H)$ which is evaluation at $\zeta$ in each coordinate level by level, is Galois-equivariant in the twisted sense $\Psi(\tau x)_\zeta = \tau\,\Psi(x)_{\tau^{-1}\zeta}$, turns `slJac q M' γ` into the level operator `levelOp q M' ζ γ⁻¹` in the $\zeta$-coordinate, and turns `diagJac q M' d` into the permutation $\zeta \mapsto \zeta^{d^{-1}}$ of coordinates. Then for every $v \in V$ which is cuspidal in the sense that $\sum_{t \in \mathbb{Z}/q} u(t)\,g\,v = 0$ for all $g \in GL_2(\mathbb{F}_q)$, and every $\zeta \in \mathrm{Idx}\,q$, the $\zeta$-coordinate `ratCoord q M' lam Ψ ζ v` $\in \mathbb{Q}_\lambda \otimes_{\mathbb{Z}_\lambda} T_\lambda(J_H)$ lies in the intersection, over all inertia elements $\tau$ at $P$ with tame character $1$, of the kernels of $s - 1$, where $s =$ `arithmeticGalois` of $\tau$ is the semilinear automorphism of `fieldBar q M'` acting coefficientwise by $\tau$ on Laurent series, acting on the rational Tate module of $\mathrm{Pic}^0$ through `rationalGaloisRep`.
--
--   This is the passage from the span (toric) hypothesis on tame inertia to invariance of the individual components: each component of a cuspidal vector in the $\lambda$-adic Tate module of the full-level Jacobian is fixed by every tame-character-trivial inertia element at a place above $q$, read through the component dictionary $\Psi$. It supplies the invariance input to the three results on the existence of a linear map on the Tate product for semistable coverings and models with inertial Igusa behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_ratCoord_mem_iInf_ker_sub_one_of_forall_sum_unipotent_eq_zero.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_DrinfeldCurve_TateRep
import Definitions.Def_ModularCurve_FullLevelCuspidalSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped TensorProduct

theorem ModularCurve.FullLevel.ratCoord_mem_iInf_ker_sub_one_of_forall_sum_unipotent_eq_zero
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (lam : ℕ) [Fact lam.Prime] (hqlam : q ≠ lam)
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ P)

    (hspan : ∀ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 →
        LinearMap.range ((ModularCurve.FullLevel.tateGal q M' lam τ).baseChange ℚ_[lam] - 1) ≤
          Submodule.span ℚ_[lam] {x : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M') |
            ∃ (g : CuspidalType.GL2 q) (v : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M')),
              (∀ t : ZMod q,
                (ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam] v = v) ∧
              (ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam] v = x})

    (Ψ : TateModule lam (ModularCurve.FullLevel.Jac q M') ≃ₗ[ℤ_[lam]]
        (ModularCurve.FullLevel.Idx q → TateModule lam (ModularCurve.FullLevel.jacComp q M')))
    (hΨ₁ : ∀ (x : TateModule lam (ModularCurve.FullLevel.Jac q M')) (ζ : ModularCurve.FullLevel.Idx q) (n : ℕ),
        ((Ψ x ζ : TateModule lam (ModularCurve.FullLevel.jacComp q M')) : ℕ → ModularCurve.FullLevel.jacComp q M') n =
          (((x : TateModule lam (ModularCurve.FullLevel.Jac q M')) : ℕ → ModularCurve.FullLevel.Jac q M') n).eval ζ)
    (hΨ₂ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : TateModule lam (ModularCurve.FullLevel.Jac q M'))
          (ζ : ModularCurve.FullLevel.Idx q),
        Ψ (ModularCurve.FullLevel.tateGal q M' lam σ x) ζ =
          ModularCurve.JH.tateGaloisRep (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') lam σ (Ψ x (σ⁻¹ • ζ)))
    (hΨ₃ : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (x : TateModule lam (ModularCurve.FullLevel.Jac q M'))
          (ζ : ModularCurve.FullLevel.Idx q),
        Ψ (ModularCurve.FullLevel.tateEnd q M' lam (ModularCurve.FullLevel.slJac q M' γ) x) ζ =
          ModularCurve.JH.tateEnd (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') lam
            (ModularCurve.FullLevel.levelOp q M' ζ γ⁻¹) (Ψ x ζ))
    (hΨ₄ : ∀ (d : (ZMod q)ˣ) (x : TateModule lam (ModularCurve.FullLevel.Jac q M')) (ζ : ModularCurve.FullLevel.Idx q),
        Ψ (ModularCurve.FullLevel.tateEnd q M' lam (ModularCurve.FullLevel.diagJac q M' d) x) ζ = Ψ x (ζ.pow d⁻¹))
    (v : ModularCurve.RationalTateModule lam (ModularCurve.FullLevel.Jac q M'))
    (hv : ∀ g : CuspidalType.GL2 q,
      (∑ t : ZMod q,
        (ModularCurve.FullLevel.tateGL2 q M' lam (CuspidalType.unipotent q t)).baseChange ℚ_[lam] *
          (ModularCurve.FullLevel.tateGL2 q M' lam g).baseChange ℚ_[lam]) v = 0)
    (ζ : ModularCurve.FullLevel.Idx q) :
    ModularCurve.FullLevel.ratCoord q M' lam Ψ ζ v ∈
      ⨅ s ∈ {s : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M') |
          ∃ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 ∧
            s = ModularCurve.arithmeticGalois
              (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ},
        LinearMap.ker (ModularCurve.rationalGaloisRep lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))
          (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) s - 1) := by sorry
