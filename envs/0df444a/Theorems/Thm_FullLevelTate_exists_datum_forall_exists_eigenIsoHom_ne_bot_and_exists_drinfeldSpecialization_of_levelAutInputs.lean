-- Prove2me | Theorems.Thm_FullLevelTate_exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_levelAutInputs
-- name    : FullLevelTate.exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_levelAutInputs
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/53508d12-1365-5aaf-9f69-20eecb069daf
-- title:
--   Full-level Tate datum: newform eigenspaces and Drinfeld specialisation
-- statement:
--   Let $q$ and $\lambda$ be primes, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $O'$ be a local commutative ring that is a $\mathbb{Z}_\lambda$-algebra with $\lambda$ in its maximal ideal. Assume the geometric inputs for the full-level-$q$ modular curve over $\Gamma_0(M')$: [`ModularCurve.FullLevel.LevelAutInputs q M'`](def/ModularCurve_FullLevelJacobian.html#L220), `HeckeGenCommute q M'` (the Hecke generators on the Jacobian commute pairwise), `GL2Laws q M'` (a $\mathrm{GL}_2(\mathbb{Z}/q)$-action on the Jacobian compatible with the $\mathrm{SL}_2(\mathbb{Z})$- and diamond actions) and [`ModularCurve.HeckeDiamondInputsHAll`](def/ModularCurve_XHOperators.html#L113) at level $q^2M'$ for the subgroup `levelH q M'`; assume further that on the $\lambda$-adic Tate module of that Jacobian the Galois action `tateGal` commutes with the $\mathrm{GL}_2(\mathbb{Z}/q)$-action `tateGL2`, the Hecke action `tateHecke` commutes with both, and `tateGal` is trivial on the inertia subgroup over $\mathbb{Q}$ of every valuation subring of $\overline{\mathbb{Q}}$ lying over any prime $\ell \neq q, \lambda$ with $\ell \nmid M'$. Then there exists a datum $D$ of type [`FullLevelTate.Datum q M' O'`](def/FullLevelTate_Datum.html#L11) — a finite free $O'$-module $V$ carrying an adically continuous Galois representation, a $\mathrm{GL}_2(\mathbb{Z}/q)$-action and a Hecke ring homomorphism, pairwise commuting, unramified outside $q$, $M'$ and the residue characteristic, and satisfying the Eichler–Shimura congruence relation — with the following two properties. First, for every $O'$-algebra structure on $\mathbb{C}$: given a weight-two cusp form $g$ on $\Gamma_0(q^2M')$ which is a newform (a normalised eigenform whose eigensystem occurs at no proper divisor level), a finite set $S$ of naturals, a ring homomorphism $\chi_g$ from the Hecke algebra of level $q^2M'$ and weight $2$ away from $S$ to $\mathbb{C}$ with $\chi_g(T_\ell) = a_\ell(g)$ for all primes $\ell \nmid q^2M'$ outside $S$, a function $\Phi$ on adelic $\mathrm{GL}_2$ over $\mathbb{Q}$ of which $g$ is an adelic lift, a $\mathbb{C}$-vector space $V$ with a $\mathrm{GL}_2(\mathbb{Q}_q)$-action commuting with scalars whose subspace of vectors fixed by `gl2CongruenceSubgroup q 1` is finite-dimensional, an injective $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariant linear map $f$ from $V$ into the adelic span of $\Phi$ whose range is the span of the orbit of the distinguished element [`LocalNewvector.AdelicSpan.self Φ`](def/LocalNewvector_AdelicSpanCarrier.html#L121), a character $\theta\colon \mathbb{F}_{q^2}^\times \to \mathbb{C}^\times$, and a subrepresentation $W$ of the reduction representation `gl2ReductionRep q V` that is cuspidal of type $\theta$ (dimension $q-1$, no nonzero unipotent-invariant vector, trivial central action, and the prescribed characteristic-polynomial identity on the nonsplit torus), there is a ring homomorphism $hk$ from [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14) to $\mathbb{C}$ sending the generator at $\ell$ to $\chi_g(T_\ell)$ for all such $\ell$, for which the $hk$-eigenspace `D.eigenIsoHom` in the space of $\mathrm{GL}_2(\mathbb{Z}/q)$-equivariant maps from $W$ to $\mathbb{C} \otimes_{O'} D.V$ is nonzero. Second, if $q \neq \lambda$ then for every field $K$ that is simultaneously an $O'$- and a $\mathbb{Q}_\lambda$-algebra with compatible structure maps on $\mathbb{Z}_\lambda$, assuming the Drinfeld coordinate ring [`DrinfeldCurve.CoordRing q (AlgebraicClosure (GaloisField q 2))`](def/DrinfeldCurve_CoordRing.html#L21) is a domain, for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $P$, every $\pi \in \overline{\mathbb{Q}}$ with $\pi^{q^2-1} = q$, and every ring homomorphism $\iota$ from $\mathbb{F}_{q^2}$ to the residue field of $P$, there is a Drinfeld specialisation $S$ of $D$ over $K$ — a finite index type together with a $K$-linear map $S.\mathrm{sp}$ from $K \otimes_{O'} D.V$ to the corresponding product of rational Tate modules of the Jacobian of the Drinfeld curve — such that: for every $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$ and every $\alpha \in \mathbb{F}_{q^2}^\times$ with $\iota(\alpha)$ equal to the tame character value $P.\mathrm{tameCharacter}\,\pi\,\tau$, and every $g \in \mathrm{GL}_2(\mathbb{Z}/q)$ with $(g,\alpha)$ in the kernel [`DrinfeldCurve.hSubgroup q`](def/DrinfeldCurve_CoordRing.html#L276) of $\det(g)\alpha^{q+1}$, the base change of $D.\mathrm{gl2}(g) \cdot D.\mathrm{gal}(\tau)$ followed by $S.\mathrm{sp}$ equals $S.\mathrm{sp}$ followed by [`DrinfeldCurve.tateProdRep`](def/DrinfeldCurve_TateRep.html#L30) at $(g,\alpha)$; and for every character $\theta\colon \mathbb{F}_{q^2}^\times \to K^\times$, every finite-dimensional $K$-representation $\sigma$ of $\mathrm{GL}_2(\mathbb{Z}/q)$ cuspidal of type $\theta$, and every $f$ in `D.isoHom` for $\sigma$, $S.\mathrm{sp} \circ f = 0$ forces $f = 0$.
--
--   This is the geometric input for level lowering at $q$: it packages the $\lambda$-adic Tate module of the Jacobian of the full-level-$q$ modular curve of level $\Gamma_0(M')$ into a datum that both receives the Hecke eigensystem of every weight-two newform of level $q^2M'$ whose local component at $q$ is supercuspidal of the given type, and admits a faithful specialisation, equivariant for the inertia at $q$ and the $\mathrm{GL}_2(\mathbb{Z}/q)$-action, into the Tate module of the Drinfeld curve. It is used by the variant [`FullLevelTate.exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_algebraMap_eq`](thm.html#FullLevelTate.exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_algebraMap_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FullLevelTate_exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_levelAutInputs.lean

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
FullLevelTate.exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_levelAutInputs
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (lam : ℕ) [Fact lam.Prime]
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
