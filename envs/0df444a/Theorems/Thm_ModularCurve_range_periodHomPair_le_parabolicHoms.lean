-- Prove2me | Theorems.Thm_ModularCurve_range_periodHomPair_le_parabolicHoms
-- name    : ModularCurve.range_periodHomPair_le_parabolicHoms
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/14f61f4e-3f01-555b-93f2-88e6d82b236b
-- title:
--   Period pairs give parabolic homomorphisms on Γ₀(N)
-- statement:
--   Let $N$ be a nonzero natural number and write $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb{Z})$ for the corresponding congruence subgroup. Consider the $\mathbb{C}$-linear map [`ModularCurve.periodHomPair N`](def/ModularCurve_PeriodHomPair.html#L135) from pairs $(f,g)$ of cusp forms of weight $2$ on $\Gamma_0(N)$ to the additive homomorphisms $\operatorname{Additive}(\Gamma_0(N)) \to \mathbb{C}$; by definition it is $0$ unless the predicate `ExistsPeriodMapLinear N` holds, i.e. unless the assignment $f \mapsto \mathrm{periodMap}\,N\,f$ is realised by some $\mathbb{C}$-linear map $\mathrm{pml}$, in which case it is the coproduct of $(\mathrm{id} + \iota^{*}) \circ \mathrm{pml}$ and $(\mathrm{id} - \iota^{*}) \circ \mathrm{pml}$, where $\iota^{*} =$ `charInvolution N ℂ ℂ` is precomposition with the additivised automorphism `jConjGamma0 N` of $\Gamma_0(N)$. The assertion is that the range of this map is contained in the submodule [`ModularCurve.Period.parabolicHoms ℂ (Gamma0 N) ℂ`](def/ModularCurve_PeriodMap.html#L62), that is, in the $\mathbb{C}$-submodule of those homomorphisms $\varphi : \operatorname{Additive}(\Gamma_0(N)) \to \mathbb{C}$ with $\varphi(\gamma) = 0$ for every $\gamma \in \Gamma_0(N)$ whose matrix satisfies $(\operatorname{tr} \gamma)^2 = 4$.
--
--   This is the elementary inclusion in the Eichler–Shimura picture: period integrals of weight-two cusp forms, and their $\pm$-eigencomponents for the conjugation involution, define classes vanishing on the elements of trace $\pm 2$, i.e. lie in the parabolic part of $\operatorname{Hom}(\Gamma_0(N),\mathbb{C})$. It is used to obtain the equality of the range with `parabolicHoms` and the resulting dimension bound $2\dim_{\mathbb{C}} S_2(\Gamma_0(N)) \le \dim_{\mathbb{C}} H^1_{\mathrm{par}}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_range_periodHomPair_le_parabolicHoms.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodHomPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.range_periodHomPair_le_parabolicHoms (N : ℕ) [NeZero N] :
    LinearMap.range (ModularCurve.periodHomPair N)
      ≤ ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma0 N) ℂ := by sorry
