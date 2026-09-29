-- Prove2me | Theorems.Thm_HeckeEis_coeffHeckeFun_projLineAlphaAdj_apply_iota0_infty_eq_heckeOperatorHom
-- name    : HeckeEis.coeffHeckeFun_projLineAlphaAdj_apply_iota0_infty_eq_heckeOperatorHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/f899e806-b727-578d-aa0a-29d969ab2e08
-- title:
--   Cochain-level Hecke equivariance of the Shapiro map at ∞
-- statement:
--   Let $N,p$ be natural numbers with $p$ nonzero and $p$ coprime to $N$, let $K$ be a commutative ring, and let $\ell$ be a nonzero natural number coprime to $Np$. Write $V=\{f\colon \mathbb{P}^1(\mathbb{Z}/p)\to K\}$, where [`ModularCurve.ProjectiveLine (ZMod p)`](def/ModularCurve_ProjectiveLine.html#L41) is the quotient of the set of unimodular rows $(a,c)$ over $\mathbb{Z}/p$ (those with $xa+yc=1$ for some $x,y$), and let $\rho$ be the representation of $\Gamma_0(N)$ on $V$ obtained by restricting [`HeckeEis.projLineRepSL p K`](def/ProjectiveLineMatrixAction.html#L124) along the inclusion of $\Gamma_0(N)$ in $\mathrm{SL}_2(\mathbb{Z})$, so that $\rho(g)f=f\circ(\text{row}\mapsto\text{row}\cdot \bar g)$, the action being vector multiplication by the reduction of $g$ mod $p$. Let $z\colon\Gamma_0(N)\to V$ be an inhomogeneous $1$-cocycle, i.e. $z(gh)=z(g)+\rho(g)(z(h))$ for all $g,h$, and let $\varphi\colon\Gamma_0(Np)\to K$ be an additive map (a homomorphism from the additivisation of $\Gamma_0(Np)$) with $\varphi(\gamma)=z(\iota_0\gamma)\bigl(\langle (0,1)\rangle\bigr)$ for all $\gamma$, where $\iota_0=$ [`Ihara.ι₀ N p`](def/IharaIota.html#L17) maps $\Gamma_0(Np)$ to $\Gamma_0(N)$ and $\langle(0,1)\rangle$ is the class of the unimodular row $(0,1)$, i.e. the point $\infty$ of $\mathbb{P}^1(\mathbb{Z}/p)$. Then for every $\gamma\in\Gamma_0(Np)$, the value at $\infty$ of $\bigl(\mathrm{coeffHeckeFun}\bigr)(\iota_0\gamma)$, namely $\sum_{q\in\Gamma_0(N)/H}\rho\bigl((\iota_0\gamma\cdot q)^{\mathrm{out}}\bigr)\Bigl(a\bigl(z(\mathrm{heckeConj}\,((\iota_0\gamma\cdot q)^{\mathrm{out}})^{-1}\,\iota_0\gamma\, q^{\mathrm{out}})\bigr)\Bigr)$ evaluated at $\infty$, with $H=$ [`HeckeEis.heckeUpper N ℓ`](def/Gamma0HeckeOperatorHom.html#L128) and $a=$ [`HeckeEis.projLineAlphaAdj p K ℓ`](def/ProjectiveLineMatrixAction.html#L152) precomposition with the action of $\mathrm{diag}(\ell,1)$ on $\mathbb{P}^1(\mathbb{Z}/p)$, equals $\bigl(\mathrm{heckeOperatorHom}\,(Np)\,\ell\,K\,\varphi\bigr)(\gamma)=\sum_{q\in\Gamma_0(Np)/H'}\varphi\bigl(\mathrm{heckeConj}_{Np,\ell}((\gamma\cdot q)^{\mathrm{out}})^{-1}\gamma\, q^{\mathrm{out}}\bigr)$, with $H'=$ [`HeckeEis.heckeUpper (N * p) ℓ`](def/Gamma0HeckeOperatorHom.html#L128).
--
--   This is the Hecke-equivariance, at the level of cochains rather than cohomology classes, of the explicit Shapiro-type comparison between $1$-cocycles of $\Gamma_0(N)$ with values in functions on $\mathbb{P}^1(\mathbb{Z}/p)$ and additive characters of $\Gamma_0(Np)$, the cocycle being evaluated at the cusp $\infty=(0:1)$. It is used in the construction of the isomorphism between the parabolic coefficient cohomology of $\Gamma_0(N)$ with $\mathbb{P}^1(\mathbb{Z}/p)$-coefficients and parabolic homomorphisms on $\Gamma_0(Np)$, [`HeckeEis.exists_coeffH1par_projLineRepSL_equiv_parabolicHoms`](thm.html#HeckeEis.exists_coeffH1par_projLineRepSL_equiv_parabolicHoms).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_coeffHeckeFun_projLineAlphaAdj_apply_iota0_infty_eq_heckeOperatorHom.lean

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_ProjectiveLineMatrixAction
import Definitions.Def_IharaIota

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.coeffHeckeFun_projLineAlphaAdj_apply_iota0_infty_eq_heckeOperatorHom (N p : ℕ) [NeZero p]
    (hpN : Nat.Coprime p N) (K : Type*) [CommRing K] (ℓ : ℕ) [NeZero ℓ] (hℓ : Nat.Coprime ℓ (N * p))
    {z : CongruenceSubgroup.Gamma0 N → ModularCurve.ProjectiveLine (ZMod p) → K}
    (hz : z ∈ HeckeEis.coeffCocycles ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (φ : Additive (CongruenceSubgroup.Gamma0 (N * p)) →+ K)
    (hφ : ∀ γ : CongruenceSubgroup.Gamma0 (N * p),
      φ (Additive.ofMul γ) = z (Ihara.ι₀ N p γ) (⟦⟨((0 : ZMod p), (1 : ZMod p)), ModularCurve.isUnimodularRow_one_right (0 : ZMod p)⟩⟧ : ModularCurve.ProjectiveLine (ZMod p)))
    (γ : CongruenceSubgroup.Gamma0 (N * p)) :
    HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.projLineAlphaAdj p K ℓ) z (Ihara.ι₀ N p γ) (⟦⟨((0 : ZMod p), (1 : ZMod p)), ModularCurve.isUnimodularRow_one_right (0 : ZMod p)⟩⟧ : ModularCurve.ProjectiveLine (ZMod p))
      = HeckeEis.heckeOperatorHom (N * p) ℓ K φ (Additive.ofMul γ) := by sorry
