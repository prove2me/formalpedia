-- Prove2me | Theorems.Thm_FullLevelTate_exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_algebraMap_eq_of_ne_two_of_cast_eq_neg_one
-- name    : FullLevelTate.exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_algebraMap_eq_of_ne_two_of_cast_eq_neg_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/1dd477ae-1d7f-5983-88d1-35a9a118c10a
-- title:
--   Full-level Tate datum with Drinfeld specialisation when q≡-1 mod λ
-- statement:
--   Let $q$ and $\lambda$ be primes with $\lambda\neq 2$ and $q\equiv-1$ in $\mathbf{Z}/\lambda$, let $M'$ be a nonzero natural number, and let $O'$ be a commutative local ring, complete and separated for the adic topology of its maximal ideal, with $\lambda$ lying in that maximal ideal. Then there is a datum $D$ of type [`FullLevelTate.Datum q M' O'`](def/FullLevelTate_Datum.html#L11), that is, a finite free $O'$-module $V$ carrying an adically continuous action `gal` of $\mathrm{Aut}(\overline{\mathbf{Q}}/\mathbf{Q})$, an action `gl2` of $\mathrm{GL}_2(\mathbf{Z}/q)$ and a ring homomorphism `hecke` from $\mathbf{Z}[T_\ell:\ell\text{ prime}]$, pairwise commuting, with inertia at primes $\ell\neq q$ not dividing $M'$ and invertible in $O'$ acting trivially and with the Eichler–Shimura relation at such $\ell$, subject to two conditions. First, for any $O'$-algebra structure on $\mathbf{C}$: given a weight-two cusp form $g$ on $\Gamma_0(q^2M')$ that is a newform (a normalised eigenform whose eigensystem occurs at no proper divisor of the level), a finite set $S$ of naturals, a ring homomorphism $\chi_g$ from the Hecke algebra of level $q^2M'$ and weight $2$ away from $S$ to $\mathbf{C}$ with $\chi_g(T_\ell)$ the $\ell$-th $q$-expansion coefficient of $g$ for all primes $\ell\nmid q^2M'$ outside $S$, a function $\Phi$ on adelic $\mathrm{GL}_2$ over $\mathbf{Q}$ of which $g$ is an adelic lift, a complex representation $V$ of $\mathrm{GL}_2(\mathbf{Q}_q)$ whose subspace of vectors fixed by the level-one congruence subgroup is finite-dimensional, an injective $\mathrm{GL}_2(\mathbf{Q}_q)$-equivariant $\mathbf{C}$-linear map $f$ from $V$ into the adelic span of $\Phi$ whose range is the span of the $\mathrm{GL}_2(\mathbf{Q}_q)$-translates of $\Phi$ itself, a character $\theta$ of $\mathbf{F}_{q^2}^\times$ with values in $\mathbf{C}^\times$, and a subrepresentation $W$ of the reduction representation of $\mathrm{GL}_2(\mathbf{Z}/q)$ on those fixed vectors which is cuspidal of type $\theta$ (dimension $q-1$, no nonzero vector fixed by all upper unipotents, scalars acting trivially, and the prescribed characteristic-polynomial identity on the nonsplit torus), there is a ring homomorphism $hk$ from $\mathbf{Z}[T_\ell:\ell\text{ prime}]$ to $\mathbf{C}$ agreeing with $\chi_g$ on $T_\ell$ for all primes $\ell\nmid q^2M'$ outside $S$ such that the $hk$-eigenspace `D.eigenIsoHom` inside the space of $\mathrm{GL}_2(\mathbf{Z}/q)$-equivariant maps from $W$ to $\mathbf{C}\otimes_{O'}V$ is nonzero. Second, if $q\neq\lambda$: for every ring homomorphism $i:\mathbf{Z}_\lambda\to O'$ and every field $K$ that is an algebra over both $O'$ and $\mathbf{Q}_\lambda$ with $\mathrm{alg}_{O'}(i(z))=\mathrm{alg}_{\mathbf{Q}_\lambda}(z)$ for all $z\in\mathbf{Z}_\lambda$, assuming the Drinfeld coordinate ring of $q$ over $\overline{\mathbf{F}_{q^2}}$ is a domain, and given a valuation subring $P$ of $\overline{\mathbf{Q}}$ in which $q$ is a nonunit, an element $\pi\in\overline{\mathbf{Q}}$ with $\pi^{q^2-1}=q$, and a ring homomorphism $\iota$ from $\mathbf{F}_{q^2}$ to the residue field of $P$, there is a Drinfeld specialisation $S$ of $D$ over $K$ at $\lambda$ and $\overline{\mathbf{F}_{q^2}}$, namely a finite index set together with a $K$-linear map $S.\mathrm{sp}$ from $K\otimes_{O'}V$ to the corresponding product of rational $\lambda$-adic Tate modules of $\mathrm{Pic}^0$ of the Drinfeld function field, such that: for every $\tau$ in the inertia subgroup of $P$ over $\mathbf{Q}$ and every $\alpha\in\mathbf{F}_{q^2}^\times$ with $\iota(\alpha)$ equal to the tame character of $P$ at $\pi$ evaluated at $\tau$, and every $g\in\mathrm{GL}_2(\mathbf{Z}/q)$ with $(g,\alpha)$ in the kernel of $(g,\alpha)\mapsto\det(g)\,\alpha^{q+1}$, the composite of the base change of `D.gl2 g * D.gal τ` followed by $S.\mathrm{sp}$ equals $S.\mathrm{sp}$ followed by the Drinfeld Tate representation at $(g,\alpha)$; and, for every character $\theta$ of $\mathbf{F}_{q^2}^\times$ with values in $K^\times$ and every finite-dimensional $K$-representation $\sigma$ of $\mathrm{GL}_2(\mathbf{Z}/q)$ cuspidal of type $\theta$, any equivariant map $f$ from $\sigma$ to $K\otimes_{O'}V$ with $f$ followed by $S.\mathrm{sp}$ zero is itself zero.
--
--   This provides the full-level Tate-module datum, with its cuspidal-type eigenclasses and its specialisation along the Drinfeld curve at $q$, used in the supercuspidal branch of level lowering at a prime dividing the level exactly twice; the additional arithmetic hypotheses $\lambda\neq 2$ and $q\equiv-1\bmod\lambda$ come from that branch. Unlike the general version it cites, no hypothesis $q\nmid M'$ is imposed: when $q\mid M'$ a newform of level $q^2M'$ admits no subrepresentation of cuspidal type in the reduction of its local component at $q$, so the first condition is vacuous. It is used in deriving the inertia labels of the residual representation attached to such a newform.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FullLevelTate_exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_algebraMap_eq_of_ne_two_of_cast_eq_neg_one.lean

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
FullLevelTate.exists_datum_forall_exists_eigenIsoHom_ne_bot_and_exists_drinfeldSpecialization_of_algebraMap_eq_of_ne_two_of_cast_eq_neg_one
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (lam : ℕ) [Fact lam.Prime] (hlam2 : lam ≠ 2) (hq1 : ((q : ℕ) : ZMod lam) = -1)
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
