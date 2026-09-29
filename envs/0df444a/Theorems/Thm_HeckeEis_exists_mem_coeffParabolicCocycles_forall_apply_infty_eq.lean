-- Prove2me | Theorems.Thm_HeckeEis_exists_mem_coeffParabolicCocycles_forall_apply_infty_eq
-- name    : HeckeEis.exists_mem_coeffParabolicCocycles_forall_apply_infty_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/7c1bcc5d-b21f-5fea-9df7-39a644d12e17
-- title:
--   Parabolic characters of Γ₀(Np) come from parabolic cocycles
-- statement:
--   Let $N$ and $p$ be natural numbers with $p$ nonzero and $p$ coprime to $N$, let $K$ be a commutative ring, and let $\varphi$ be an additive-group homomorphism from the additivisation of $\Gamma_0(Np) \le \mathrm{SL}_2(\mathbb{Z})$ to $K$ which is parabolic, i.e. $\varphi(\gamma) = 0$ for every $\gamma \in \Gamma_0(Np)$ whose underlying integral matrix satisfies $\operatorname{tr}(\gamma)^2 = 4$. Consider the representation of $\Gamma_0(N)$ on the $K$-module of functions $\mathbb{P}^1(\mathbb{Z}/p) \to K$ obtained by restricting [`HeckeEis.projLineRepSL p K`](def/ProjectiveLineMatrixAction.html#L124) along the inclusion of $\Gamma_0(N)$ into $\mathrm{SL}_2(\mathbb{Z})$, where $g$ acts on $f$ by $(\rho(g) f)(P) = f(\mathrm{projLineAct}\, p\, g\, P)$, the latter being right multiplication of the unimodular row $P$ by the reduction of $g$ modulo $p$ when that reduction has unit determinant and the identity otherwise. Then there exists $z \colon \Gamma_0(N) \to (\mathbb{P}^1(\mathbb{Z}/p) \to K)$ such that (i) $z$ is an inhomogeneous $1$-cocycle, $z(gh) = z(g) + \rho(g)(z(h))$ for all $g, h \in \Gamma_0(N)$; (ii) $z$ is parabolic, i.e. $z(\gamma) \in \operatorname{range}(\rho(\gamma) - 1)$ whenever $\operatorname{tr}(\gamma)^2 = 4$; and (iii) for every $\gamma \in \Gamma_0(Np)$, evaluating $z$ at the image of $\gamma$ under the map [`Ihara.ι₀ N p`](def/IharaIota.html#L17) into $\Gamma_0(N)$ and then at the class of the unimodular row $(0,1)$, i.e. the point $\infty = (0:1)$ of $\mathbb{P}^1(\mathbb{Z}/p)$, gives $\varphi(\gamma)$.
--
--   This is the surjectivity half, with the parabolic refinement, of the explicit Shapiro isomorphism relating parabolic $1$-cocycles of $\Gamma_0(N)$ with values in the induced module $K[\mathbb{P}^1(\mathbb{Z}/p)]$ to additive characters of $\Gamma_0(Np)$. It feeds into [`HeckeEis.exists_coeffH1par_projLineRepSL_equiv_parabolicHoms`](thm.html#HeckeEis.exists_coeffH1par_projLineRepSL_equiv_parabolicHoms), where the comparison of the two parabolic cohomology groups is assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_mem_coeffParabolicCocycles_forall_apply_infty_eq.lean

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

theorem HeckeEis.exists_mem_coeffParabolicCocycles_forall_apply_infty_eq (N p : ℕ) [NeZero p]
    (hpN : Nat.Coprime p N) (K : Type*) [CommRing K]
    (φ : Additive (CongruenceSubgroup.Gamma0 (N * p)) →+ K)
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 (N * p)) K) :
    ∃ z : CongruenceSubgroup.Gamma0 N → ModularCurve.ProjectiveLine (ZMod p) → K,
      z ∈ HeckeEis.coeffParabolicCocycles ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype) ∧
      ∀ γ : CongruenceSubgroup.Gamma0 (N * p),
        z (Ihara.ι₀ N p γ) (⟦⟨((0 : ZMod p), (1 : ZMod p)), ModularCurve.isUnimodularRow_one_right (0 : ZMod p)⟩⟧ : ModularCurve.ProjectiveLine (ZMod p)) = φ (Additive.ofMul γ) := by sorry
