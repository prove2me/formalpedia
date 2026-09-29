-- Prove2me | Theorems.Thm_HeckeEis_coeffH1par_map_heckeT_comm
-- name    : HeckeEis.coeffH1par_map_heckeT_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/08f2087c-284f-5aa2-b92a-542ff3cb8bb4
-- title:
--   Coefficient change is Hecke-equivariant on parabolic H¹
-- statement:
--   Let $R,R'$ be commutative rings, $\varphi : R \to R'$ a ring homomorphism, and $n,N,\ell$ natural numbers with $\ell \neq 0$. For a commutative ring $K$ write $\rho_K$ for the representation of $\Gamma_0(N)$ obtained by restricting along $\Gamma_0(N) \hookrightarrow \mathrm{SL}(2,\mathbb{Z})$ the action of $\mathrm{SL}(2,\mathbb{Z})$ on the degree-$n$ homogeneous part of $K[X_0,X_1]$ by the substitution $X_j \mapsto \sum_i M_{ij} X_i$, and write $H^1_{\mathrm{par}}$ for [`HeckeEis.coeffH1par`](def/Gamma0CoeffCohomology.html#L100) of $\rho_K$, the quotient of the module of parabolic cocycles (functions $z : \Gamma_0(N) \to \mathrm{Sym}^n$ with $z(gh) = z(g) + \rho_K(g)z(h)$ and $z(\gamma) \in \mathrm{range}(\rho_K(\gamma) - 1)$ whenever $\mathrm{tr}(\gamma)^2 = 4$) by the coboundaries contained in it. Assume given: an additive map $\Phi$ from $H^1_{\mathrm{par}}$ over $R$ to $H^1_{\mathrm{par}}$ over $R'$ such that every parabolic cocycle $z$ over $R$ admits a parabolic cocycle $w$ over $R'$ with $w(g) = \mathrm{map}\,\varphi\,(z(g))$ for all $g \in \Gamma_0(N)$ and $\Phi[z] = [w]$; an $R$-linear endomorphism $T$ of $H^1_{\mathrm{par}}$ over $R$ such that every parabolic cocycle $z$ admits a parabolic cocycle $w$ equal, as a function, to [`HeckeEis.coeffHeckeFun N ℓ`](def/Gamma0CoeffCohomology.html#L129) applied to $z$ with coefficient part the substitution by $\mathrm{diag}(\ell,1)$, and $T[z] = [w]$; and an $R'$-linear endomorphism $T'$ of $H^1_{\mathrm{par}}$ over $R'$ with the same property over $R'$. Then $T'(\Phi x) = \Phi(T x)$ for every $x$ in $H^1_{\mathrm{par}}$ over $R$.
--
--   This expresses the Hecke-equivariance of change of coefficient ring on the parabolic cohomology of $\Gamma_0(N)$ with binary-form coefficients, the operators $T,T'$ and the map $\Phi$ being specified only through their effect on cocycle representatives. It is used when comparing eigenclasses over different coefficient rings, for instance in the construction of integral structures on spaces of cusp forms and in the passage from an eigenform to an eigenclass over $\mathbb{Z}$ or over a residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_coeffH1par_map_heckeT_comm.lean

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.coeffH1par_map_heckeT_comm {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (n N ℓ : ℕ) [NeZero ℓ]
    (Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ g : CongruenceSubgroup.Gamma0 N, ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R' n)) g : MvPolynomial (Fin 2) R')
            = MvPolynomial.map φ (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R n)) g : MvPolynomial (Fin 2) R))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (T : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[R] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hT : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R n)) = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj R n ℓ) z ∧
        T (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (T' : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[R'] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hT' : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R' n)) = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj R' n ℓ) z ∧
        T' (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)) :
    T' (Φ x) = Φ (T x) := by sorry
