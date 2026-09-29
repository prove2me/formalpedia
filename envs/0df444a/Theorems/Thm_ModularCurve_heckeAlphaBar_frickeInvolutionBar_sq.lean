-- Prove2me | Theorems.Thm_ModularCurve_heckeAlphaBar_frickeInvolutionBar_sq
-- name    : ModularCurve.heckeAlphaBar_frickeInvolutionBar_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/632ccc5d-3f0f-59e7-916a-8046f575753a
-- title:
--   Fricke conjugation swaps the two degeneracy maps at level p²
-- statement:
--   Let $p$ be a prime. Work inside Laurent series over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, and write $\overline{F}_N$ for `modularFunctionFieldBar N`, the intermediate field `laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)`, i.e. the subfield of `LaurentSeries (AlgebraicClosure ℚ)` generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of `modularFunctionFieldFull N`, the latter being the subfield of `LaurentSeries ℚ` obtained by adjoining `divisorExpansions N` to $\mathbb{Q}$. Three maps occur: `heckeAlphaBar (AlgebraicClosure ℚ) p p`, the $\overline{\mathbb{Q}}$-algebra inclusion $\overline{F}_p \hookrightarrow \overline{F}_{p\cdot p}$ coming from the containment of the level-$p$ field in the level-$p^2$ field; `heckeBetaBar (AlgebraicClosure ℚ) p p`, the $\overline{\mathbb{Q}}$-algebra map $\overline{F}_p \to \overline{F}_{p\cdot p}$ induced by `qExpand`, the substitution multiplying all Laurent exponents by $p$ (that is, $q \mapsto q^p$); and `frickeInvolutionBar N`, the $\overline{\mathbb{Q}}$-automorphism of $\overline{F}_N$ obtained by base change along `geomAut` from `frickeInvolutionFull N`, a chosen $\mathbb{Q}$-automorphism of `modularFunctionFieldFull N` satisfying `IsFrickeAutFull N` when one exists and the identity otherwise. The assertion is that for every $x \in \overline{F}_p$,
--   $$\alpha\bigl(\overline{w}_p(x)\bigr) = \overline{w}_{p^2}\bigl(\beta(x)\bigr),$$
--   with $\alpha$, $\beta$ and $\overline{w}_N$ the three maps just described.
--
--   This is the classical compatibility stating that conjugating by the Fricke involutions at levels $p$ and $p^2$ interchanges the two degeneracy maps $X_0(p^2) \rightrightarrows X_0(p)$, one given by the inclusion of function fields and the other by $q \mapsto q^p$. It is used in the computation of the divisor of the Hecke correspondence at level $p$, in [`ModularCurve.heckeDivBar_self_add_frickeInvolutionBar_smul`](thm.html#ModularCurve.heckeDivBar_self_add_frickeInvolutionBar_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeAlphaBar_frickeInvolutionBar_sq.lean

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.heckeAlphaBar_frickeInvolutionBar_sq (p : ℕ) [hp : Fact (Nat.Prime p)] (x : modularFunctionFieldBar p) : heckeAlphaBar (AlgebraicClosure ℚ) p p (frickeInvolutionBar p x) = frickeInvolutionBar (p * p) (heckeBetaBar (AlgebraicClosure ℚ) p p x) := by sorry
