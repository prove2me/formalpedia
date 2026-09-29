-- Prove2me | Theorems.Thm_HeckeEis_exists_coeffH1_dual_ne_zero_isCoeffHeckeOnH1_eq_qCoeff_smul_of_isCuspidalOfType
-- name    : HeckeEis.exists_coeffH1_dual_ne_zero_isCoeffHeckeOnH1_eq_qCoeff_smul_of_isCuspidalOfType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/508c6679-2f31-532b-b6a5-971cfa2169f5
-- title:
--   Newform eigensystem in H¹ with dual cuspidal-type coefficients
-- statement:
--   Let $N \ge 1$ and let $q$ be a prime with $q \nmid N$. Let $g$ be a weight-$2$ cusp form on $\Gamma_0(Nq^2)$ which is a newform, i.e. a normalised eigenform whose good eigensystem occurs at no proper divisor $M$ of $Nq^2$, and let $\Phi$ be a function on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ that is an adelic lift of $g$: left invariant under the global points, right invariant under the level-one subgroup attached to $Nq^2$, and equal, on elements with trivial finite part, to the weight-$2$ slash of $g$ evaluated at $i$. Let $V$ be a complex vector space with a $\mathrm{GL}_2(\mathbb{Q}_q)$-action commuting with the scalars, such that the submodule of vectors fixed by the congruence subgroup [`FLT.SmoothVectors.gl2CongruenceSubgroup q 1`](def/RepTheory_GL2CongruenceSubgroup.html#L181) (matrices $g$ with all entries of $g-1$ and of $g^{-1}-1$ of norm at most $q^{-1}$) is finite dimensional, and let $f : V \to$ [`LocalNewvector.AdelicSpan`](def/LocalNewvector_AdelicSpanCarrier.html#L82) $\Phi$ be an injective $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariant linear map whose range is the $\mathbb{C}$-span of the translates of the distinguished element [`LocalNewvector.AdelicSpan.self`](def/LocalNewvector_AdelicSpanCarrier.html#L121) $\Phi$. Let $\theta : \mathbb{F}_{q^2}^\times \to \mathbb{C}^\times$ be a character and assume the representation $W :=$ [`LocalNewvector.gl2ReductionRep`](def/LocalNewvector_ReductionFunctor.html#L187) $q\,V$ of $\mathrm{GL}_2(\mathbb{Z}/q)$ on the fixed submodule is cuspidal of type $\theta$: its rank is $q-1$, no nonzero vector is fixed by all unipotents, the scalar elements act as the identity, and for every $\alpha \in \mathbb{F}_{q^2}^\times$ the characteristic polynomial of the torus element $\alpha$ times $(X - \theta(\alpha))(X - \theta(\alpha)^{-1})$ equals that of the corresponding induced representation. Finally let $\mathrm{red} : \Gamma_0(N) \to \mathrm{GL}_2(\mathbb{Z}/q)$ be reduction modulo $q$, given as the inclusion $\Gamma_0(N) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ followed by reduction and the map to $\mathrm{GL}_2$. Then there is a nonzero class $x$ in [`HeckeEis.coeffH1`](def/Gamma0CoeffCohomologyEigen.html#L16) of the representation $W^\vee \circ \mathrm{red}$ of $\Gamma_0(N)$ (cocycles modulo coboundaries for the dual of the fixed submodule) such that for every prime $\ell$ with $\ell \nmid Nq^2$ and $\ell \not\equiv 0 \pmod q$, and every $\mathbb{C}$-linear endomorphism $T$ of this $H^1$ satisfying [`HeckeEis.IsCoeffHeckeOnH1`](def/Gamma0CoeffCohomologyEigen.html#L61) $N\,\ell$ for the coefficient map $W^\vee(\mathrm{diag}(\ell,1))$ — that is, every cocycle $z$ has $\mathrm{coeffHeckeFun}\,N\,\ell$ applied to it again a cocycle, representing $T$ of the class of $z$ — one has $T x = a_\ell(g)\, x$, where $a_\ell(g)$ is the $\ell$-th coefficient of the level-one $q$-expansion of $g$.
--
--   This records that the Hecke eigensystem of a weight-$2$ newform of level $Nq^2$ whose local representation at $q$ is cuspidal of type $\theta$ is realised by a nonzero class in the first cohomology of $\Gamma_0(N)$ with coefficients in the dual of that type, the Hecke action away from $Nq^2$ being the cochain-level operators with the prescribed coefficient map. It is the form in which the type-theoretic transfer of eigenvalues is used in the passage to cohomology of $\Gamma_H$-level groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_coeffH1_dual_ne_zero_isCoeffHeckeOnH1_eq_qCoeff_smul_of_isCuspidalOfType.lean

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem
HeckeEis.exists_coeffH1_dual_ne_zero_isCoeffHeckeOnH1_eq_qCoeff_smul_of_isCuspidalOfType
    (N : ℕ) [NeZero N] {q : ℕ} [Fact q.Prime]
    (hqN : ¬ q ∣ N)
    (g : CuspForm (Gamma0 (N * q ^ 2)) 2) (hg : g.IsNewform)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    [FiniteDimensional ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
    (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ) (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
    (hfi : Function.Injective f)
    (hfr : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (θ : (GaloisField q 2)ˣ →* ℂˣ) (hθ : CuspidalType.IsCuspidalOfType θ (LocalNewvector.gl2ReductionRep q V))
    (red : Gamma0 N →* CuspidalType.GL2 q)
    (hred : red = (Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype) :
    ∃ x : HeckeEis.coeffH1 ((LocalNewvector.gl2ReductionRep q V).dual.comp red), x ≠ 0 ∧
      ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q ^ 2 → ∀ h : ((ℓ : ZMod q) ≠ 0),
        ∀ T : HeckeEis.coeffH1 ((LocalNewvector.gl2ReductionRep q V).dual.comp red) →ₗ[ℂ]
            HeckeEis.coeffH1 ((LocalNewvector.gl2ReductionRep q V).dual.comp red),
          HeckeEis.IsCoeffHeckeOnH1 N ℓ ((LocalNewvector.gl2ReductionRep q V).dual.comp red)
              ((LocalNewvector.gl2ReductionRep q V).dual (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h))) T →
            T x = ModularFormClass.qCoeff g ℓ • x := by sorry
