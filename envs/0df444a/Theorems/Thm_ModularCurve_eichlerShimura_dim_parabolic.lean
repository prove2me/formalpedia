-- Prove2me | Theorems.Thm_ModularCurve_eichlerShimura_dim_parabolic
-- name    : ModularCurve.eichlerShimura_dim_parabolic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/242696db-13fc-5845-af10-9fce886a8c5c
-- title:
--   Dimension of parabolic homomorphisms for Γ₀(N)
-- statement:
--   Let $N$ be a natural number, assumed nonzero. Consider the complex vector space of additive group homomorphisms from the group $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb{Z})$, written additively via `Additive`, to $\mathbb{C}$, and inside it the submodule [`ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma0 N) ℂ`](def/ModularCurve_PeriodMap.html#L62) consisting of those homomorphisms $\varphi$ satisfying the predicate `IsParabolicHom`, i.e. $\varphi(\gamma) = 0$ for every $\gamma \in \Gamma_0(N)$ whose underlying integral $2 \times 2$ matrix has $(\operatorname{tr}\gamma)^2 = 4$. The theorem asserts the equality of natural numbers
--   $$\dim_{\mathbb{C}} \big(\text{parabolic homomorphisms } \Gamma_0(N) \to \mathbb{C}\big) = 2 \cdot \dim_{\mathbb{C}} S_2(\Gamma_0(N)),$$
--   where the right-hand side uses the Mathlib space `CuspForm (CongruenceSubgroup.Gamma0 N) 2` of weight-two cusp forms on $\Gamma_0(N)$, and both dimensions are `Module.finrank`, so that the convention $\mathrm{finrank} = 0$ applies to any infinite-dimensional space. Since a homomorphism from $\Gamma_0(N)$ to the abelian group $\mathbb{C}$ factors through the abelianisation, the left-hand side is the dimension of the parabolic cohomology $H^1_{\mathrm{par}}(\Gamma_0(N), \mathbb{C})$ with trivial coefficients, the parabolicity condition being imposed here by vanishing on all elements of trace $\pm 2$.
--
--   This is the dimension formula extracted from the Eichler–Shimura isomorphism $H^1_{\mathrm{par}}(\Gamma_0(N), \mathbb{C}) \cong S_2(\Gamma_0(N)) \oplus \overline{S_2(\Gamma_0(N))}$ in weight two, in the form of an equality of complex dimensions rather than an explicit (Hecke-equivariant) isomorphism. It supports the identification of the image of the period pair map with the parabolic part, used in [`ModularCurve.periodHomPair_range_eq_parabolicHoms`](thm.html#ModularCurve.periodHomPair_range_eq_parabolicHoms).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eichlerShimura_dim_parabolic.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodHomPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.eichlerShimura_dim_parabolic (N : ℕ) [NeZero N] :
    Module.finrank ℂ ↥(ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma0 N) ℂ)
      = 2 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) := by sorry
