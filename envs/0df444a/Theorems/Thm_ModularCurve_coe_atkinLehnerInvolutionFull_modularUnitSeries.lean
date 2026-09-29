-- Prove2me | Theorems.Thm_ModularCurve_coe_atkinLehnerInvolutionFull_modularUnitSeries
-- name    : ModularCurve.coe_atkinLehnerInvolutionFull_modularUnitSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/eed1fc31-da5d-5574-8dd2-845829a87f4e
-- title:
--   Partial Atkin–Lehner involution takes u_Q to Q¹²u_Q⁻¹
-- statement:
--   Let $d,Q$ be nonzero natural numbers. Inside the Laurent series field $\mathbb{Q}((q))$ write $j(q^e)$ for `qExpand ℚ e jq`, the image of the $q$-expansion of $j$ under $q \mapsto q^{e}$, and let $F =$ `modularFunctionFieldFull (d * Q)` be the intermediate field obtained by adjoining to $\mathbb{Q}$ all $j(q^{e})$ with $e \neq 0$ and $e \mid dQ$. Let $u_Q =$ `modularUnitSeries Q` be $\Delta(q)\cdot\Delta(q^{Q})^{-1}$, where $\Delta(q)$ is the Laurent series $q$ times the power series `dedekindEtaUnitQ` and $\Delta(q^{Q})$ is its image under $q \mapsto q^{Q}$. Two hypotheses are assumed: first, that there exists a $\mathbb{Q}$-algebra automorphism $\sigma$ of $F$ satisfying `IsAtkinLehnerAutFull d Q`, i.e. interchanging $j(q^{e})$ and $j(q^{eQ})$ for every nonzero divisor $e$ of $d$; second, that $u_Q$ lies in $F$. Let $w_Q =$ `atkinLehnerInvolutionFull d Q`, which is by definition such a $\sigma$, chosen arbitrarily when one exists and the identity otherwise. Then the Laurent series underlying $w_Q(u_Q)$ equals $Q^{12}\cdot u_Q^{-1}$, the scalar $(Q:\mathbb{Q})^{12}$ acting on the inverse of $u_Q$ in $\mathbb{Q}((q))$.
--
--   Classically $F$ is the function field of $X_0(dQ)$, $u_Q = (\eta(\tau)/\eta(Q\tau))^{24}$ is Ogg's modular unit, and the hypothesis on $\sigma$ expresses that $w_Q$ is the partial Atkin–Lehner involution at $Q$; the transformation $\Delta(-1/\tau) = \tau^{12}\Delta(\tau)$ accounts for the factor $Q^{12}$. The identity is used in the analysis of places and cusps of the modular curve, in particular in the statements about prolongation tuples and the behaviour of orders at the cusp $\infty$ that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coe_atkinLehnerInvolutionFull_modularUnitSeries.lean

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_AtkinLehnerPartial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.coe_atkinLehnerInvolutionFull_modularUnitSeries (d Q : ℕ) [NeZero d] [NeZero Q]
    (hσ : ∃ σ : ModularCurve.modularFunctionFieldFull (d * Q) ≃ₐ[ℚ]
        ModularCurve.modularFunctionFieldFull (d * Q), ModularCurve.IsAtkinLehnerAutFull d Q σ)
    (hmem : ModularCurve.modularUnitSeries Q ∈ ModularCurve.modularFunctionFieldFull (d * Q)) :
    ((ModularCurve.atkinLehnerInvolutionFull d Q ⟨ModularCurve.modularUnitSeries Q, hmem⟩ :
        ModularCurve.modularFunctionFieldFull (d * Q)) : LaurentSeries ℚ)
      = (Q : ℚ) ^ 12 • (ModularCurve.modularUnitSeries Q)⁻¹ := by sorry
