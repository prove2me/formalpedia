-- Prove2me | Theorems.Thm_HeckeEis_isEigensystemH1_of_H1_gammaH_dual_of_isCuspidalOfType_of_qCoeff_congr
-- name    : HeckeEis.isEigensystemH1_of_H1_gammaH_dual_of_isCuspidalOfType_of_qCoeff_congr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/8808e8bc-0c68-51b4-bded-a7953597347b
-- title:
--   Residual H¹ eigensystem at level N from a cuspidal type
-- statement:
--   Fix $N\ge 1$ and a prime $q$. Let $g$ be a cusp form of weight $2$ on $\Gamma_0(Nq^2)$ which is a newform in the sense that it is a normalised Hecke eigenform ($a_1=1$, multiplicativity on coprime indices and the two recursions at primes dividing and not dividing the level) and no such eigensystem agreeing with that of $g$ at primes not dividing $Nq^2$ occurs at a proper divisor of the level, and let $\Phi$ be a function on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ which is an adelic lift of $g$: left invariant under the global points $\mathrm{GL}_2(\mathbb{Q})$, right invariant under the level-one subgroup at level $N q^2$, and equal to $(g\mid_2 h_\infty)(i)$ on adelic matrices with trivial finite part and positive archimedean part. Let $V$ be a complex vector space with a $\mathbb{C}$-commuting action of $\mathrm{GL}_2(\mathbb{Q}_q)$ whose subspace $V^{K_1}$ of vectors fixed by the congruence subgroup [`FLT.SmoothVectors.gl2CongruenceSubgroup q 1`](def/RepTheory_GL2CongruenceSubgroup.html#L181) is finite dimensional, and let $f:V\to$ [`LocalNewvector.AdelicSpan`](def/LocalNewvector_AdelicSpanCarrier.html#L82) $\Phi$ be an injective $\mathrm{GL}_2(\mathbb{Q}_q)$-equivariant linear map whose range is the $\mathbb{C}$-span of the $\mathrm{GL}_2(\mathbb{Q}_q)$-translates of the distinguished element of that span attached to $\Phi$. Let $\theta:\mathbb{F}_{q^2}^\times\to\mathbb{C}^\times$ and assume the representation [`LocalNewvector.gl2ReductionRep q V`](def/LocalNewvector_ReductionFunctor.html#L187) of $\mathrm{GL}_2(\mathbb{Z}/q)$ on $V^{K_1}$ is cuspidal of type $\theta$: it has dimension $q-1$, only the zero vector is fixed by all upper unipotents, scalars act trivially, and for every $\alpha\in\mathbb{F}_{q^2}^\times$ the characteristic polynomial of the torus element $\alpha$ times $(X-\theta(\alpha))(X-\theta(\alpha)^{-1})$ is the characteristic polynomial of $\alpha$ acting in the permutation representation on the projective line over $\mathbb{Z}/q$. Let `red` $:\Gamma_0(N)\to\mathrm{GL}_2(\mathbb{Z}/q)$ be reduction modulo $q$, let $H_1\le(\mathbb{Z}/Nq^2)^\times$ be the kernel of reduction to $(\mathbb{Z}/q)^\times$, and let `conj` be a homomorphism from $\ker(\mathrm{red})$ into $\Gamma_{H_1}(Nq^2)$ whose entries satisfy $a\mapsto a$, $qb'=b$, $c'=qc$, $d\mapsto d$ (conjugation by $\mathrm{diag}(q,1)$). Let $\varphi$ be a nonzero additive homomorphism from $\Gamma_{H_1}(Nq^2)$ to the $\mathbb{C}$-dual of $V^{K_1}$ which is equivariant for the dual of `gl2ReductionRep` along `red` on conjugates inside $\ker(\mathrm{red})$, and which satisfies, for every prime $\ell\nmid Nq^2$ with $\ell\not\equiv 0 \pmod q$, the eigenvalue relation that the transfer Hecke operator [`CohCarrier.heckeT`](def/CohCarrier_Level.html#L250) at $\ell$ applied to $\varphi$, followed by the dual of `gl2ReductionRep` at $\mathrm{diag}(\ell,1)$, equals $a_\ell(g)\varphi$. Finally fix a prime $p$, a field $\kappa$ of characteristic $p$, an ideal $\mathfrak{m}$ of the algebraic integers in $\mathbb{C}$ arising as the kernel of a ring homomorphism to $\kappa$, a set $S_0$ of primes containing $q$, and integers $b_\ell$ such that for every prime $\ell\nmid Nq^2$ with $\ell\notin S_0$ the eigenvalue $a_\ell(g)$ is an algebraic integer congruent to $b_\ell$ modulo $\mathfrak{m}$; assume $\theta\ne 1$ and $\theta^{p^n}=1$ for some $n$. Then there exist a finite-dimensional $\kappa$-vector space $V_\sigma$ and a representation $\sigma$ of $\mathrm{GL}_2(\mathbb{Z}/q)$ on it such that the characteristic polynomial of every group element in the permutation representation $\kappa[\mathbb{P}^1(\mathbb{Z}/q)]$ equals $(X-1)^2$ times its characteristic polynomial in $\sigma$, and such that [`HeckeEis.IsEigensystemH1`](def/Gamma0CoeffCohomologyEigen.html#L72) holds for $\Gamma_0(N)$ acting through $\sigma\circ\mathrm{red}$, with coefficient operators $\sigma(\mathrm{diag}(\ell,1))$ when $\ell\not\equiv0\pmod q$ and the identity otherwise, with exceptional set $S_0$ and eigenvalues the images of $b_\ell$ in $\kappa$: there is a nonzero class in the coefficient cohomology $H^1$ of $\Gamma_0(N)$ which, for each prime $\ell\nmid N$ outside $S_0$, is an eigenvector with eigenvalue $b_\ell$ for some endomorphism realising the Hecke correspondence at $\ell$ on that cohomology.
--
--   This is the descent step in the level-lowering argument at a prime $q$ of depth-zero supercuspidal type: the occurrence of a cuspidal type $\theta$ in the cohomology of $\Gamma_{H_1}(Nq^2)$ with coefficients dual to the local new-vector space is converted, after reduction modulo a maximal ideal of the algebraic integers, into a mod $p$ Hecke eigensystem on the first cohomology of $\Gamma_0(N)$ with coefficients in a reduction $\sigma$ of the type. It feeds the construction of eigensystems attached to semistable models of elliptic curves with prescribed Frobenius traces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_isEigensystemH1_of_H1_gammaH_dual_of_isCuspidalOfType_of_qCoeff_congr.lean

import Definitions.Def_CohCarrier_Level
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
open CongruenceSubgroup Polynomial

theorem
HeckeEis.isEigensystemH1_of_H1_gammaH_dual_of_isCuspidalOfType_of_qCoeff_congr
    (N : ℕ) [NeZero N] {q : ℕ} [Fact q.Prime]
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
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)
    (H₁ : Subgroup (ZMod (N * q ^ 2))ˣ)
    (hH₁ : H₁ = (ZMod.unitsMap ((dvd_pow_self q two_ne_zero).mul_left N)).ker)
    (conj : ↥red.ker →* ↥(CohCarrier.GammaH (N * q ^ 2) H₁))
    (hconj : ∀ x : ↥red.ker,
      (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 = ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0 ∧
      (q : ℤ) * (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 =
        ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1 ∧
      (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 =
        (q : ℤ) * ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 ∧
      (conj x : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1 =
        ((x : Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1)
    (φ : CohCarrier.H1 (N * q ^ 2) H₁
        (Module.Dual ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)))
    (hφ0 : φ ≠ 0)
    (hφeq : ∀ (γ y : Gamma0 N) (hy : y ∈ red.ker) (hy' : γ * y * γ⁻¹ ∈ red.ker),
        φ (Additive.ofMul (conj ⟨γ * y * γ⁻¹, hy'⟩)) =
          (LocalNewvector.gl2ReductionRep q V).dual (red γ) (φ (Additive.ofMul (conj ⟨y, hy⟩))))
    (hφT : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q ^ 2 → ∀ h : ((ℓ : ZMod q) ≠ 0),
        ((LocalNewvector.gl2ReductionRep q V).dual
            (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h))).toAddMonoidHom.comp
          (CohCarrier.heckeT (N * q ^ 2) H₁ ℓ
            (Module.Dual ℂ ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)) φ) =
          ModularFormClass.qCoeff g ℓ • φ)
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] (𝔪 : Ideal (integralClosure ℤ ℂ))
    (red𝔪 : integralClosure ℤ ℂ →+* κ) (hker𝔪 : RingHom.ker red𝔪 = 𝔪)
    (S₀ : Set ℕ) (hqS₀ : q ∈ S₀) (b : ℕ → ℤ)
    (hcong : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * q ^ 2 → ℓ ∉ S₀ →
      ∃ c : integralClosure ℤ ℂ, (c : ℂ) = ModularFormClass.qCoeff g ℓ ∧ c - (b ℓ : integralClosure ℤ ℂ) ∈ 𝔪)
    (hθ1 : θ ≠ 1) (hθp : ∃ n : ℕ, θ ^ p ^ n = 1)
:
    ∃ (Vσ : Type) (_ : AddCommGroup Vσ) (_ : Module κ Vσ) (_ : FiniteDimensional κ Vσ)
      (σ : Representation κ (CuspidalType.GL2 q) Vσ),
      (∀ g' : CuspidalType.GL2 q,
      LinearMap.charpoly (CuspidalType.ind q κ g') = (X - 1) ^ 2 * LinearMap.charpoly (σ g')) ∧
      HeckeEis.IsEigensystemH1 N (σ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
        (fun ℓ : ℕ =>
          if h : ((ℓ : ZMod q) ≠ 0) then σ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
        S₀ (fun ℓ => ((b ℓ : ℤ) : κ)) := by sorry
