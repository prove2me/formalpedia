-- Prove2me | Theorems.Thm_HeckeEis_coeffH1Mk_cocycle_heckeTLin_modularForm
-- name    : HeckeEis.coeffH1Mk_cocycle_heckeTLin_modularForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/e71e30cd-e198-590c-a5c4-2d544597ae06
-- title:
--   Hecke equivariance of Eichler integrals on H¹(Γ₀(N),Symⁿ)
-- statement:
--   Fix $N \ge 1$, an integer $n \ge 0$ and a prime $\ell$ with $\ell \nmid N$, and let $\rho$ be the representation of $\Gamma_0(N)$ obtained by restricting to $\Gamma_0(N)$ the action of $SL(2,\mathbb{Z})$ on the space of degree-$n$ homogeneous forms in $\mathbb{C}[X_0,X_1]$ by the substitution $X_j \mapsto \sum_i g_{ij} X_i$. Here $H^1$ is realised as `coeffH1` $\rho$, the quotient of the module of inhomogeneous cocycles $z : \Gamma_0(N) \to \mathrm{Sym}^n$ satisfying $z(gh) = z(g) + \rho(g) z(h)$ by the submodule of coboundaries. Let $T$ be a $\mathbb{C}$-linear endomorphism of this $H^1$ which is a Hecke operator at level of cochains in the sense of `IsCoeffHeckeOnH1`: for every cocycle $z$ there is a cocycle $w$ whose underlying function is the explicit transfer sum `coeffHeckeFun` $N\,\ell\,\rho\,a\,z$ over $\Gamma_0(N)/\,$`heckeUpper`$\,N\,\ell$, with coefficient part $a =$ `binaryFormAlphaAdj`, the substitution $P(X_0,X_1) \mapsto P(\ell X_0, X_1)$, and such that $T[z] = [w]$. Let $f$ be a modular form of weight $n+2$ on $\Gamma_0(N)$ and let $F : \mathbb{H} \to \mathrm{Sym}^n$ be an Eichler integral of $f$, i.e. for every multidegree $d$ and every $\tau$ the coefficient function $z \mapsto \mathrm{coeff}_d F(z)$ has derivative $f(\tau)\,\mathrm{coeff}_d\big((\tau X_0 + X_1)^n\big)$ at $\tau$, and assume $F$ is an equivariant primitive for $\rho$: for each $\gamma \in \Gamma_0(N)$ the difference $F(\gamma \tau) - \rho(\gamma) F(\tau)$ is independent of $\tau$. Let $F'$ satisfy the same two conditions with $f$ replaced by [`ModularForm.heckeTLin`](def/ModularForm_HeckeOperatorForms.html#L20) $(n+2)$ applied to $f$, the Hecke operator at $\ell$ on weight $n+2$ forms of level $N$. Then $T$ sends the class of the cocycle $\gamma \mapsto F(\gamma \cdot i) - \rho(\gamma) F(i)$ attached to $F$ to the class of the corresponding cocycle attached to $F'$.
--
--   This is the Hecke equivariance of the Eichler–Shimura construction, stated for all modular forms of weight $n+2$ on $\Gamma_0(N)$ and for the full (not parabolic) coefficient cohomology, with no twist for these normalisations of $T_\ell$ and of the coefficient action. It is used to transport eigenform relations $T_\ell f = \lambda f$ into eigenvector relations for the associated cohomology classes, and is cited in the construction of eigensystems in $H^1$ attached to modular and to mod $p$ forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_coeffH1Mk_cocycle_heckeTLin_modularForm.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_HeckeEis_EichlerIntegral
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold MatrixGroups

theorem HeckeEis.coeffH1Mk_cocycle_heckeTLin_modularForm (N : ℕ) [NeZero N] (n : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N)
    (T : HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[ℂ]
      HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hT : haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      HeckeEis.IsCoeffHeckeOnH1 N ℓ ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        (HeckeEis.binaryFormAlphaAdj ℂ n ℓ) T)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2))
    (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)) (hEI : HeckeEis.IsEichlerIntegral n f F)
    (hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F)
    (F' : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (hEI' : HeckeEis.IsEichlerIntegral n (ModularForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f) F')
    (hF' : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F') :
    T (HeckeEis.coeffH1Mk ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        ⟨hF.cocycle, hF.cocycle_mem_coeffCocycles⟩) =
      HeckeEis.coeffH1Mk ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        ⟨hF'.cocycle, hF'.cocycle_mem_coeffCocycles⟩ := by sorry
