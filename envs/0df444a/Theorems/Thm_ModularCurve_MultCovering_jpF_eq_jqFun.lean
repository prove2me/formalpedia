-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_jpF_eq_jqFun
-- name    : ModularCurve.MultCovering.jpF_eq_jqFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/14e60391-f482-55ff-a075-ed32380ce113
-- title:
--   The two spellings of j(qᵖ) at level 1· p agree
-- statement:
--   Let $p$ be a prime. Both sides of the asserted equality are elements of `modularFunctionFieldBar (1 * p)`, the intermediate field of $\overline{\mathbb Q}((q))$ obtained by base change along $\mathbb Q \to \overline{\mathbb Q}$ of the full modular function field of level index $1\cdot p$; such an element is a Laurent series over $\overline{\mathbb Q}$ together with a proof that it lies in that field. On the left, `jpF p` is the element whose underlying series is the coefficientwise image under $\mathbb Q \to \overline{\mathbb Q}$ (the map `coeffEmb`) of `qExpand ℚ p jq`, that is of the $q$-expansion of $j$ with the substitution $q \mapsto q^{p}$, the exponent-scaling operator `qExpand ℚ p` being multiplication by $p$ on the index monoid $\mathbb Z$; its membership is witnessed through the divisibility $p \mid 1\cdot p$ in the form `dvd_mul_left p 1`. On the right, `PlaceSpecialization.jqFun` with parameter $q := p$ is the element whose underlying series is the `coeffEmb`-image of `qExpand ℚ (1 * p) jq`, with membership witnessed through `dvd_refl (1 * p)`. The theorem asserts that these two elements are equal.
--
--   This is a bookkeeping identity reconciling the two names under which the function $j(q^{p})$ occurs in the project: the spelling used in the charts of the prime-level multiplicative covering, indexed by $p$, and the spelling used by the level-one prolongation pair, indexed by $1\cdot p$. It is invoked by the lemmas that pass between the covering charts (residues, cusp charts, the tie element $j(q^{p})-j^{p}$) and the prolongation pair's dictionary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_jpF_eq_jqFun.lean

import Definitions.Def_ModularCurve_MultCoveringCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.jpF_eq_jqFun (p : ℕ) [Fact p.Prime] : jpF p = PlaceSpecialization.jqFun (q := p) := by sorry
