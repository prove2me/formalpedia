-- Prove2me | Theorems.Thm_GaloisRep_residual_framed_isEquiv_baseChangeAlong
-- name    : GaloisRep.residual_framed_isEquiv_baseChangeAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/2134916d-1743-51b6-992a-412e92d78a8e
-- title:
--   Residual representation of a framed lift of ρ₀
-- statement:
--   Let $\mathcal O$ be a commutative local ring with residue field $k =$ `IsLocalRing.ResidueField 𝒪`, let $\bar\rho$ be a residual Galois representation over $k$, i.e. a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\bar\rho\colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \mathrm{End}_k(V)$ factoring through a finite level, let $\rho_0$ be a continuous monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{GL}_2$ of the pro-Artinian object [`Deformation.ProartinianCat.residueField`](def/Deformations_ProartinianCat.html#L188) (whose carrier is $k$ with the discrete topology), and let $b$ be a basis of $V$ indexed by `Fin 2` such that for every $\sigma$ the matrix underlying $\rho_0(\sigma)$ is the matrix of $\bar\rho(\sigma)$ in the basis $b$. Let $R$ be an object of [`Deformation.ProartinianCat 𝒪`](def/Deformations_ProartinianCat.html#L44) (a local pro-Artinian topological $\mathcal O$-algebra) and let $\rho^{u}\colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \mathrm{GL}_2(R)$ be a continuous monoid homomorphism lying in the value at $R$ of the subfunctor [`Deformation.liftFunctor`](def/Deformations_LiftFunctor.html#L62) cut out by $\rho_0$, that is, the pushforward of $\rho^{u}$ along the unique morphism from $R$ to the terminal object `residueField` equals $\rho_0$. Assume further that the resulting action on $R^2 = (\mathrm{Fin}\ 2 \to R)$, obtained from $\rho^u$ by passing to the underlying matrices and then to endomorphisms, is adically continuous: for every $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak m_R^{\,n}\cdot R^2$ for all $v$. Then the residual representation of the rank-two adically continuous representation $(R^2, \rho)$, namely $\mathrm{ResidueField}(R)\otimes_R R^2$ with the base-changed action, is equivalent (there exists a $\mathrm{ResidueField}(R)$-linear isomorphism commuting with the two Galois actions) to $\bar\rho$ base-changed along the induced map $k \to \mathrm{ResidueField}(R)$ on residue fields.
--
--   This is the statement that a framed lift of $\rho_0$ over a pro-Artinian $\mathcal O$-algebra $R$ has residual representation $\bar\rho \otimes_k k_R$, i.e. that such a lift really lifts $\bar\rho$; it is the glue between the matrix-valued lifting functor and the module-valued notion of an adically continuous Galois representation. It supplies the 'lifts $\bar\rho$' component in the construction of the deformation-ring data used by [`GaloisRep.nonempty_deformationRingData`](thm.html#GaloisRep.nonempty_deformationRingData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_residual_framed_isEquiv_baseChangeAlong.lean

import Mathlib
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ProartinianCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits IsLocalRing Deformation Deformation.ProartinianCat

theorem GaloisRep.residual_framed_isEquiv_baseChangeAlong
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪))
    (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) (Deformation.ProartinianCat.residueField (𝓞 := 𝒪)))
    (b : Module.Basis (Fin 2) (IsLocalRing.ResidueField 𝒪) ρbar.V)
    (hρ₀ : ∀ σ, (ρ₀ σ).val = LinearMap.toMatrix b b (ρbar.ρ σ))
    {R : Deformation.ProartinianCat 𝒪}
    (ρu : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) R)
    (hρu : ρu ∈ (Deformation.liftFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪 ρ₀).obj R)
    (hcont : GaloisActionIsAdicContinuous R
      ((Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom))) :
    ({ V := Fin 2 → R, finrank_eq := by simp,
       ρ := (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom),
       isAdicContinuous := hcont } : GaloisRepAdic R).residual.IsEquiv
      (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 R))) := by sorry
