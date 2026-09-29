-- Prove2me | Theorems.Thm_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH
-- name    : ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/bbb54472-bf30-5c91-a18b-f8523fb4d51f
-- title:
--   Petersson functional in the period lattice of Γ_H(M)
-- statement:
--   Fix a natural number $M \neq 0$ and a subgroup $H \le (\mathbb{Z}/M)^\times$, and let $\Gamma =$ [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) be the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained by taking the preimage of $H$ under the determinant-style character $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$, $\gamma \mapsto \gamma_{22} \bmod M$, and pushing it forward along the inclusion $\Gamma_0(M) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$. Let $f$ be a weight-$2$ cusp form for $\Gamma$. For $\gamma \in \Gamma$, [`ModularCurve.periodOf`](def/ModularCurve_PeriodOf.html#L56) is the $\mathbb{C}$-linear functional on weight-$2$ cusp forms for $\Gamma$ given by integrating along the path from $i$ to $\gamma \cdot i$ in the upper half-plane, and the period lattice is the $\mathbb{Z}$-submodule of the dual spanned by these functionals. The theorem asserts the equivalence of two statements: first, that there is an element $\Lambda$ of this period lattice such that for every weight-$2$ cusp form $g$ for $\Gamma$ one has $i \int f(\tau)\overline{g(\tau)}(\operatorname{Im}\tau)^2 = \Lambda(g)$, the integral being taken over [`FLT.Gamma0FundamentalSet.gammaFundamentalSet`](def/AutomorphicForm_Gamma0FundamentalSet.html#L13) of $\Gamma \vee \langle -1 \rangle$, i.e. the union over cosets $q$ of $\mathrm{SL}_2(\mathbb{Z})/(\Gamma\{\pm 1\})$ of the translates $q^{-1} \cdot \mathcal{D}$ of the standard fundamental domain by chosen coset representatives; and second, that $\operatorname{Re}$ of the period of $f$ along $\gamma$ is an integer for every $\gamma \in \Gamma$.
--
--   This is the integrality criterion on $\Gamma_H(M)$ for the Petersson functional of a weight-$2$ cusp form to be a period, i.e. the statement that under the Riemann form attached to the Petersson product the period lattice of $X_H(M)$ is its own dual. It is used in the computation of the multiplier of norm-one elements whose Abel–Jacobi image lies in the period lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

theorem ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) 2) :
    (∃ Λ ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H), ∀ g : CuspForm (CohCarrier.GammaH M H) 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))), UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = Λ g) ↔
      ∀ γ : CohCarrier.GammaH M H, ∃ m : ℤ, (ModularCurve.periodOf (CohCarrier.GammaH M H) γ f).re = m := by sorry
