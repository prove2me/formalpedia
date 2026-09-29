-- Prove2me | Theorems.Thm_ModularCurve_dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0
-- name    : ModularCurve.dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/2ce1ed64-8cdd-574d-99d7-02f3ead4fec5
-- title:
--   Degree at least ψ(M) over K(j) for X₀(M)
-- statement:
--   Let $K$ be a field and $M$ a positive integer whose image in $K$ is nonzero. Let $F =$ [`ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)`](def/ModularCurve_X1.html#L101) be the intermediate field of the Laurent series field `LaurentSeries K` generated over $K$ by the set of all quotients $\overline{p_f}/\overline{p_g}$, where $f,g$ are modular forms of one and the same weight $k \in \mathbb{Z}$ for $\Gamma_0(M)$ regarded inside $\mathrm{GL}_2(\mathbb{R})$, $p_f, p_g$ are power series over $\mathbb{Z}$ satisfying `IsIntegralQExp f pf` and `IsIntegralQExp g pg`, and the coefficientwise image $\overline{p_g}$ of $p_g$ in $K$ is nonzero. Let $x \in F$ be an element whose underlying Laurent series is [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15), that is $q^{-1}$ times the image in $K$ of the power series $E_4^3 \eta^{-24}$ (the $q$-expansion of the modular invariant $j$). Assume that $F$ is finite-dimensional over the intermediate field $K(x)$ obtained by adjoining $x$ to $K$ inside $F$. Then $\psi(M) \le [F : K(x)]$, where $\psi(M)$ is [`ModularCurve.dedekindPsi M`](def/ModularCurve_X0.html#L201), defined as $\sum_{d \mid M,\ d \text{ squarefree}} M/d$.
--
--   This is Igusa's lower bound for the degree of $X_0(M)$ over the $j$-line, in $q$-expansion form and over an arbitrary coefficient field in which $M$ is invertible. It is used in the computation of relative degrees and indices for the congruence subgroups $\Gamma_0$ and $\Gamma_H$, and in the local analysis of valuation subrings on $X_0(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0
    (K : Type*) [Field K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (x : ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))
    (hx : (x : LaurentSeries K) = ModularCurve.jqModC K)
    [FiniteDimensional
      (IntermediateField.adjoin K
        ({x} : Set (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))))
      (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))] :
    ModularCurve.dedekindPsi M ≤
      Module.finrank
        (IntermediateField.adjoin K
          ({x} : Set (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))))
        (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)) := by sorry
