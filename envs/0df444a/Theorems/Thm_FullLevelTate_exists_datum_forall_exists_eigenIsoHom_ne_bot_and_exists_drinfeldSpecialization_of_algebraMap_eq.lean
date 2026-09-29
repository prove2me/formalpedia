-- Prove2me | Theorems.Thm_FullLevelTate_exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_algebraMap_eq
-- name    : FullLevelTate.exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_algebraMap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/37373583-cd05-517e-aeb3-79cfefc7f15c
-- title:
--   A full-level Tate datum receiving newforms and Drinfeld specialisations
-- statement:
--   Let $q$ and $\lambda$ be primes, $M'$ a nonzero natural number, and $O'$ a commutative local ring that is adically complete for its maximal ideal and in which $\lambda$ lies in the maximal ideal. Then there is a datum $D$ of type [`FullLevelTate.Datum q M' O'`](def/FullLevelTate_Datum.html#L11) — a finite free $O'$-module $D.V$ carrying an adically continuous action `gal` of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, an action `gl2` of $\mathrm{GL}_2(\mathbb{Z}/q)$ and a ring homomorphism `hecke` from the polynomial Hecke ring $\mathbb{Z}[T_\ell:\ell\text{ prime}]$, the three pairwise commuting, with `gal` trivial on the inertia subgroup of any valuation subring of $\overline{\mathbb{Q}}$ lying over a prime $\ell\neq q$ not dividing $M'$ and invertible in $O'$, and satisfying at such $\ell$ the Eichler–Shimura relation $\mathrm{gal}(\sigma)^2-\mathrm{hecke}(T_\ell)\mathrm{gal}(\sigma)+\ell\cdot\mathrm{gl2}(\ell)=0$ for $\sigma$ a Frobenius at $\ell$ — with the following two properties. First, for any $O'$-algebra structure on $\mathbb{C}$: given a weight-two cusp form $g$ on $\Gamma_0(q^2M')$ that is a newform (a normalised eigenform whose eigensystem does not already occur at a proper divisor of the level), a finite set $S$ of naturals, a ring homomorphism $\chi_g$ from the Hecke algebra of level $q^2M'$ away from $S$ to $\mathbb{C}$ with $\chi_g(T_\ell)$ equal to the $\ell$-th $q$-expansion coefficient of $g$ for every prime $\ell\nmid q^2M'$ outside $S$, a function $\Phi$ on adelic $\mathrm{GL}_2$ over $\mathbb{Q}$ of which $g$ is an adelic lift, a $\mathbb{C}$-vector space $V$ with a $\mathrm{GL}_2(\mathbb{Q}_q)$-action commuting with the scalars and with finite-dimensional subspace of vectors fixed by the first congruence subgroup, an injective $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariant $\mathbb{C}$-linear map $f$ from $V$ into the adelic span of $\Phi$ whose image is the span of the $\mathrm{GL}_2(\mathbb{Q}_q)$-translates of the distinguished element of that span, a character $\theta:\mathbb{F}_{q^2}^\times\to\mathbb{C}^\times$, and a subrepresentation $W$ of the reduction representation `gl2ReductionRep` of $V$ that is cuspidal of type $\theta$ (dimension $q-1$, no nonzero unipotent-invariant vector, trivial central action, and the prescribed torus characteristic-polynomial identity), there is a ring homomorphism $hk$ from the polynomial Hecke ring to $\mathbb{C}$ with $hk(T_\ell)=\chi_g(T_\ell)$ for all primes $\ell\nmid q^2M'$ outside $S$ such that the $hk$-eigensubmodule of the space of maps $W\to\mathbb{C}\otimes_{O'}D.V$ intertwining $W$ (restricted along the inclusion of the top subgroup of $\mathrm{GL}_2(\mathbb{Z}/q)$) with `gl2` is nonzero. Second, if $q\neq\lambda$: for every ring homomorphism $i:\mathbb{Z}_\lambda\to O'$ and every field $K$ that is an algebra over both $O'$ and $\mathbb{Q}_\lambda$ with the two structure maps agreeing along $i$ on $\mathbb{Z}_\lambda$, assuming the Drinfeld coordinate ring [`DrinfeldCurve.CoordRing`](def/DrinfeldCurve_CoordRing.html#L21) of $q$ over $\overline{\mathbb{F}_{q^2}}$ is a domain, then for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $P$, every $\pi\in\overline{\mathbb{Q}}$ with $\pi^{q^2-1}=q$, and every ring homomorphism $\iota:\mathbb{F}_{q^2}\to$ the residue field of $P$, there is a Drinfeld specialisation $S$ of $D$ over $K$ — a finite index type together with a $K$-linear map $S.\mathrm{sp}$ from $K\otimes_{O'}D.V$ to the corresponding product of copies of $K\otimes_{\mathbb{Q}_\lambda}$ the rational $\lambda$-adic Tate module of $\mathrm{Pic}^0$ of the Drinfeld function field — such that, first, for every $\tau$ in the inertia subgroup of $P$ over $\mathbb{Q}$ and every $\alpha\in\mathbb{F}_{q^2}^\times$ with $\iota(\alpha)$ equal to the tame character of $P$ at $\pi$ evaluated on $\tau$, and every $g\in\mathrm{GL}_2(\mathbb{Z}/q)$ with $(g,\alpha)$ in the kernel of $\det(g)\cdot\alpha^{q+1}$, the base change to $K$ of $D.\mathrm{gl2}(g)D.\mathrm{gal}(\tau)$ followed by $S.\mathrm{sp}$ equals $S.\mathrm{sp}$ followed by the Tate product representation at $(g,\alpha)$; and second, for every $\theta:\mathbb{F}_{q^2}^\times\to K^\times$ and every finite-dimensional $K$-representation $\sigma$ of $\mathrm{GL}_2(\mathbb{Z}/q)$ cuspidal of type $\theta$, every intertwiner $f$ from $\sigma$ (restricted along the top subgroup) to $K\otimes_{O'}D.V$ with $f$ followed by $S.\mathrm{sp}$ zero is itself zero.
--
--   This is the existence statement for the global object used in the study of inertia at $q$ for newforms of level $q^2M'$ whose local component at $q$ has cuspidal type: a Tate-module datum with commuting Galois, $\mathrm{GL}_2(\mathbb{Z}/q)$ and Hecke actions, realising every such newform in a Hecke eigenspace of its cuspidal-type isotypic space, and specialising at $q$ into copies of the $\lambda$-adic Tate module of the Jacobian of the Drinfeld curve. No coprimality of $q$ and $M'$ is assumed, the cuspidal-type clause being vacuous when $q \mid M'$. It is the input to the determination of the tame inertia labels at $q$, which is the local ingredient of level lowering at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FullLevelTate_exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_algebraMap_eq.lean

import Definitions.Def_FullLevelTate_IsoHom
import Definitions.Def_FullLevelTate_DrinfeldSpecialization
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
FullLevelTate.exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_algebraMap_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (lam : ℕ) [Fact lam.Prime]
    (O' : Type) [CommRing O'] [IsLocalRing O'] [IsAdicComplete (IsLocalRing.maximalIdeal O') O']
    (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O') :
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
      (q ≠ lam → ∀ (i : ℤ_[lam] →+* O') (K : Type) [Field K] [Algebra O' K] [Algebra ℚ_[lam] K],
        (∀ z : ℤ_[lam], algebraMap O' K (i z) = algebraMap ℚ_[lam] K (z : ℚ_[lam])) →
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
