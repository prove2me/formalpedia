-- Prove2me | Theorems.Thm_FullLevelTate_exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_levelAutInputs_of_ne_two_of_cast_eq_neg_one
-- name    : FullLevelTate.exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_levelAutInputs_of_ne_two_of_cast_eq_neg_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/a72b1f40-37d3-59e0-befc-9cb0138076f8
-- title:
--   Existence of a full-level Tate datum with Drinfeld specialisation
-- statement:
--   Let $q$ be a prime, $M'$ a positive integer with $q \nmid M'$, and $\lambda$ a prime with $\lambda \neq 2$ and $q \equiv -1 \pmod{\lambda}$; let $O'$ be a local commutative ring which is a $\mathbb{Z}_\lambda$-algebra with $\lambda$ in its maximal ideal. Assume, for the Jacobian [`ModularCurve.FullLevel.Jac q M'`](def/ModularCurve_FullLevelJacobian.html#L85) and its $\lambda$-adic Tate module: the predicates [`ModularCurve.FullLevel.LevelAutInputs q M'`](def/ModularCurve_FullLevelJacobian.html#L220), [`ModularCurve.FullLevel.HeckeGenCommute q M'`](def/ModularCurve_FullLevelJacobian.html#L315) (the Hecke generators on the Jacobian commute) and [`ModularCurve.FullLevel.GL2Laws q M'`](def/ModularCurve_FullLevelJacobian.html#L255) (existence of a $\mathrm{GL}_2(\mathbb{F}_q)$-action on the Jacobian compatible with the $\Gamma_0(M')$-level automorphisms and the diamond operators); the predicate [`ModularCurve.HeckeDiamondInputsHAll`](def/ModularCurve_XHOperators.html#L113) for the level $q^2M'$ with the subgroup [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22); that `tateGal` commutes with `tateGL2`, and that `tateHecke` commutes with both `tateGal` and `tateGL2`; and that for every prime $\ell \neq q, \lambda$ with $\ell \nmid M'$ the operator `tateGal q M' lam σ` is the identity for every $\sigma$ in the inertia subgroup over $\mathbb{Q}$ of every valuation subring of $\overline{\mathbb{Q}}$ lying over $\ell$. Then there exists a datum $D$ of type [`FullLevelTate.Datum q M' O'`](def/FullLevelTate_Datum.html#L11) (a finite free $O'$-module $D.V$ carrying commuting actions of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, of $\mathrm{GL}_2(\mathbb{F}_q)$ and of the Hecke algebra [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14) $= \mathbb{Z}[X_\ell]$, with adic continuity, inertial triviality away from $q$, $M'$ and the residue characteristic, and the Eichler–Shimura relation) with the following two properties. First, for any $O'$-algebra structure on $\mathbb{C}$: given a weight-two cusp form $g$ on $\Gamma_0(q^2M')$ which is a newform (a normalised eigenform whose eigensystem occurs at no proper divisor of the level), a finite set $S$ of naturals, a ring homomorphism $\chi_g$ from [`CuspForm.heckeAlgebra (q ^ 2 * M') 2 S`](def/CuspForm_HeckeAlgebra.html#L18) to $\mathbb{C}$ with $\chi_g(T_\ell) = a_\ell(g)$ for all primes $\ell \nmid q^2M'$ with $\ell \notin S$, a function $\Phi$ on adelic $\mathrm{GL}_2$ over $\mathbb{Q}$ of which $g$ is an adelic lift, a $\mathbb{C}$-vector space $V$ with a $\mathrm{GL}_2(\mathbb{Q}_q)$-action commuting with the scalars and with finite-dimensional space of vectors fixed by [`FLT.SmoothVectors.gl2CongruenceSubgroup q 1`](def/RepTheory_GL2CongruenceSubgroup.html#L181), an injective equivariant $\mathbb{C}$-linear map $f : V \to$ [`LocalNewvector.AdelicSpan`](def/LocalNewvector_AdelicSpanCarrier.html#L82) $\Phi$ whose range is the span of the $\mathrm{GL}_2(\mathbb{Q}_q)$-orbit of [`LocalNewvector.AdelicSpan.self`](def/LocalNewvector_AdelicSpanCarrier.html#L121) $\Phi$, a character $\theta : \mathbb{F}_{q^2}^\times \to \mathbb{C}^\times$ and a subrepresentation $W$ of the reduction representation [`LocalNewvector.gl2ReductionRep q V`](def/LocalNewvector_ReductionFunctor.html#L187) which is cuspidal of type $\theta$ (dimension $q-1$, no nonzero unipotent-invariant vector, trivial central action, and the prescribed torus characteristic polynomials), there is a ring homomorphism $hk :$ [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14) $\to \mathbb{C}$ with $hk(X_\ell) = \chi_g(T_\ell)$ for all such $\ell$, for which the $hk$-eigenspace `D.eigenIsoHom` inside the space of $\mathrm{GL}_2(\mathbb{F}_q)$-equivariant maps $W \to \mathbb{C} \otimes_{O'} D.V$ is nonzero. Secondly, if $q \neq \lambda$ then for every field $K$ which is both an $O'$- and a $\mathbb{Q}_\lambda$-algebra, compatibly over $\mathbb{Z}_\lambda$, with [`DrinfeldCurve.CoordRing q`](def/DrinfeldCurve_CoordRing.html#L21) over $\overline{\mathbb{F}_{q^2}}$ a domain, every valuation subring $P$ of $\overline{\mathbb{Q}}$ lying over $q$, every $\pi \in \overline{\mathbb{Q}}$ with $\pi^{q^2-1} = q$ and every ring homomorphism $\iota : \mathbb{F}_{q^2} \to$ the residue field of $P$, there is a Drinfeld specialisation $S$ of $D$ over $K$ (a finite index set together with a $K$-linear map $S.sp$ from $K \otimes_{O'} D.V$ to the corresponding product of rational Tate modules of the Drinfeld curve) such that: for $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$ and $\alpha \in \mathbb{F}_{q^2}^\times$ with $\iota(\alpha)$ equal to the tame character value `P.tameCharacter π τ`, and for every $g \in \mathrm{GL}_2(\mathbb{F}_q)$ with $(g,\alpha)$ in the kernel [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276) of $(g,\alpha) \mapsto \det(g)\,\alpha^{q+1}$, one has $S.sp \circ (D.gl2\,g \cdot D.gal\,\tau)_K =$ [`DrinfeldCurve.tateProdRep`](def/DrinfeldCurve_TateRep.html#L30) applied to $(g,\alpha)$, composed after $S.sp$; and $S.sp$ is injective on equivariant maps out of cuspidal representations, in the sense that for every $\theta : \mathbb{F}_{q^2}^\times \to K^\times$, every finite-dimensional $K$-representation $\sigma$ of $\mathrm{GL}_2(\mathbb{F}_q)$ cuspidal of type $\theta$ and every $f$ in `D.isoHom`, $S.sp \circ f = 0$ forces $f = 0$.
--
--   This packages the Jacobian of the full-level-$q$, $\Gamma_0(M')$ modular curve, together with its $\lambda$-adic Tate module and the Galois, $\mathrm{GL}_2(\mathbb{F}_q)$ and Hecke actions on it, into a single datum which both receives the weight-two newforms of level $q^2M'$ of a given cuspidal type at $q$ and admits a specialisation to the Tate module of the Drinfeld curve, the latter computing the inertia at $q$ in tame terms. It is the form of the construction used in the supercuspidal branch of level lowering at a prime dividing the level exactly twice, under the arithmetic restrictions $\lambda \neq 2$ and $q \equiv -1 \pmod{\lambda}$, and is invoked by the variant in which the $\mathbb{Z}_\lambda$-compatibility is supplied as a hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FullLevelTate_exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_levelAutInputs_of_ne_two_of_cast_eq_neg_one.lean

import Definitions.Def_FullLevelTate_IsoHom
import Definitions.Def_FullLevelTate_DrinfeldSpecialization
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem
FullLevelTate.exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_levelAutInputs_of_ne_two_of_cast_eq_neg_one
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (lam : ℕ) [Fact lam.Prime] (hlam2 : lam ≠ 2) (hq1 : ((q : ℕ) : ZMod lam) = -1)
    (O' : Type) [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[lam] O']
    (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hHC : ModularCurve.FullLevel.HeckeGenCommute q M')
    (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (hin : ModularCurve.HeckeDiamondInputsHAll (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
    (hGG : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : CuspidalType.GL2 q),
      ModularCurve.FullLevel.tateGal q M' lam σ * ModularCurve.FullLevel.tateGL2 q M' lam x =
        ModularCurve.FullLevel.tateGL2 q M' lam x * ModularCurve.FullLevel.tateGal q M' lam σ)
    (hTGal : ∀ (t : ModularCurve.HeckeAlg) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ModularCurve.FullLevel.tateHecke q M' lam t * ModularCurve.FullLevel.tateGal q M' lam σ =
        ModularCurve.FullLevel.tateGal q M' lam σ * ModularCurve.FullLevel.tateHecke q M' lam t)
    (hTG : ∀ (t : ModularCurve.HeckeAlg) (x : CuspidalType.GL2 q),
      ModularCurve.FullLevel.tateHecke q M' lam t * ModularCurve.FullLevel.tateGL2 q M' lam x =
        ModularCurve.FullLevel.tateGL2 q M' lam x * ModularCurve.FullLevel.tateHecke q M' lam t)
    (hunr : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ q → ¬ ℓ ∣ M' → ℓ ≠ lam →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ModularCurve.FullLevel.tateGal q M' lam σ = 1) :
    ∃ D : FullLevelTate.Datum q M' O',
      (∀ [Algebra O' ℂ]
          (g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2) (_ : g.IsNewform)
          (S : Finset ℕ) (chig : CuspForm.heckeAlgebra (q ^ 2 * M') 2 (↑S : Set ℕ) →+* ℂ)
          (_ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ q ^ 2 * M') (hℓS : ℓ ∉ (↑S : Set ℕ)),
            chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
          (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (_ : g.IsAdelicLiftOf Φ)
          (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
          [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
          [FiniteDimensional ℂ
            ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
          (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ)
          (_ : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v) (_ : Function.Injective f)
          (_ : LinearMap.range f =
            Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
          (θ : (GaloisField q 2)ˣ →* ℂˣ)
          (W : Subrepresentation (LocalNewvector.gl2ReductionRep q V))
          (_ : CuspidalType.IsCuspidalOfType θ W.toRepresentation),
          ∃ hk : ModularCurve.HeckeAlg →+* ℂ,
            (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ q ^ 2 * M') (hℓS : ℓ ∉ (↑S : Set ℕ)),
                hk (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) = chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) ∧
              D.eigenIsoHom ℂ (W.toRepresentation.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype) hk ≠ ⊥) ∧
      (q ≠ lam → ∀ (K : Type) [Field K] [Algebra O' K] [Algebra ℚ_[lam] K],
        (∀ z : ℤ_[lam], algebraMap O' K (algebraMap ℤ_[lam] O' z) = algebraMap ℚ_[lam] K (z : ℚ_[lam])) →
        ∀ [IsDomain (DrinfeldCurve.CoordRing q (AlgebraicClosure (GaloisField q 2)))]
        (P : ValuationSubring (AlgebraicClosure ℚ)), P.LiesOverPrime q →
        ∀ (π : AlgebraicClosure ℚ), π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) →
        ∀ ι : GaloisField q 2 →+* IsLocalRing.ResidueField P,
          ∃ S : D.DrinfeldSpecialization K lam (AlgebraicClosure (GaloisField q 2)),
            (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
              ι (α : GaloisField q 2) = P.tameCharacter π τ →
                ∀ (g : CuspidalType.GL2 q) (hg : (g, α) ∈ DrinfeldCurve.hSubgroup q),
                  S.sp ∘ₗ ((D.gl2 g * D.gal τ).baseChange K) =
                    DrinfeldCurve.tateProdRep q (AlgebraicClosure (GaloisField q 2)) lam K S.index ⟨(g, α), hg⟩ ∘ₗ
                      S.sp) ∧
            (∀ (θ : (GaloisField q 2)ˣ →* Kˣ) {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
              (σ : Representation K (CuspidalType.GL2 q) W), CuspidalType.IsCuspidalOfType θ σ →
                ∀ f : ↥(D.isoHom K (σ.comp (⊤ : Subgroup (CuspidalType.GL2 q)).subtype)),
                  S.sp ∘ₗ (f : W →ₗ[K] K ⊗[O'] D.V) = 0 → f = 0)) := by sorry
