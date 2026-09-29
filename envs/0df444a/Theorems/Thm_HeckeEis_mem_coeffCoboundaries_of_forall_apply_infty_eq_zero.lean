-- Prove2me | Theorems.Thm_HeckeEis_mem_coeffCoboundaries_of_forall_apply_infty_eq_zero
-- name    : HeckeEis.mem_coeffCoboundaries_of_forall_apply_infty_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/0134dfe6-18a0-5e97-b81d-4fada724465b
-- title:
--   Cocycles vanishing at ∞ on Γ₀(Np) are coboundaries
-- statement:
--   Let $N,p$ be natural numbers with $p \neq 0$ and $\gcd(p,N)=1$, and let $K$ be a commutative ring. Consider the representation of $\Gamma_0(N)$ on the $K$-module of functions $\mathbb{P}^1(\mathbb{Z}/p) \to K$ obtained by restricting [`HeckeEis.projLineRepSL p K`](def/ProjectiveLineMatrixAction.html#L124) along the inclusion of $\Gamma_0(N)$ into $\mathrm{SL}(2,\mathbb{Z})$; here $\mathbb{P}^1(\mathbb{Z}/p)$ is the set of rows $(a,c)$ over $\mathbb{Z}/p$ admitting $x,y$ with $xa+yc=1$, modulo the defining setoid, and $g$ sends $f$ to $P \mapsto f(P \cdot \bar{g})$, the action being by right multiplication of the reduction of $g$ modulo $p$. Let $z : \Gamma_0(N) \to (\mathbb{P}^1(\mathbb{Z}/p) \to K)$ be an inhomogeneous $1$-cocycle, i.e. $z(gh) = z(g) + g \cdot z(h)$ for all $g,h \in \Gamma_0(N)$. Assume that for every $\gamma \in \Gamma_0(Np)$ the value $z(\mathrm{\iota_0}(\gamma))$, where $\mathrm{\iota_0}$ denotes the map [`Ihara.ι₀ N p`](def/IharaIota.html#L17) from $\Gamma_0(Np)$ to $\Gamma_0(N)$, vanishes at the point $\infty = (0 : 1)$ of $\mathbb{P}^1(\mathbb{Z}/p)$. Then $z$ lies in the image of the coboundary map, that is, there exists $F : \mathbb{P}^1(\mathbb{Z}/p) \to K$ with $z(g) = g \cdot F - F$ for all $g \in \Gamma_0(N)$.
--
--   This is the injectivity half of the explicit Shapiro isomorphism for the pair $\Gamma_0(Np) \le \Gamma_0(N)$: the evaluation-at-$\infty$ map from $1$-cocycles valued in the induced module of functions on $\mathbb{P}^1(\mathbb{Z}/p)$ to homomorphisms on $\Gamma_0(Np)$ kills only coboundaries. It is used in the construction of the isomorphism between the parabolic coefficient cohomology of [`HeckeEis.projLineRepSL`](def/ProjectiveLineMatrixAction.html#L124) and parabolic homomorphisms, [`HeckeEis.exists_coeffH1par_projLineRepSL_equiv_parabolicHoms`](thm.html#HeckeEis.exists_coeffH1par_projLineRepSL_equiv_parabolicHoms).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_mem_coeffCoboundaries_of_forall_apply_infty_eq_zero.lean

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

theorem HeckeEis.mem_coeffCoboundaries_of_forall_apply_infty_eq_zero (N p : ℕ) [NeZero p] (hpN : Nat.Coprime p N)
    (K : Type*) [CommRing K]
    {z : CongruenceSubgroup.Gamma0 N → ModularCurve.ProjectiveLine (ZMod p) → K}
    (hz : z ∈ HeckeEis.coeffCocycles ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hz0 : ∀ γ : CongruenceSubgroup.Gamma0 (N * p),
      z (Ihara.ι₀ N p γ) (⟦⟨((0 : ZMod p), (1 : ZMod p)), ModularCurve.isUnimodularRow_one_right (0 : ZMod p)⟩⟧ : ModularCurve.ProjectiveLine (ZMod p)) = 0) :
    z ∈ HeckeEis.coeffCoboundaries ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype) := by sorry
