-- Prove2me | Theorems.Thm_ModularCurve_frickeInvolutionBar_comp_heckeBetaBar_one
-- name    : ModularCurve.frickeInvolutionBar_comp_heckeBetaBar_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/d4607aa7-7484-5e00-8086-c4d591a876a8
-- title:
--   Fricke involution sends the second degeneracy leg to the first
-- statement:
--   Let $q$ be a nonzero natural number. Write $F^{\mathrm{full}}_N = \mathbb{Q}(\mathrm{divisorExpansions}\,N) \subseteq \mathbb{Q}((t))$ for the intermediate field `modularFunctionFieldFull N` of the Laurent series field, and let $\overline{F}_N$ denote `laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)`, the subfield of $\overline{\mathbb{Q}}((t))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of $F^{\mathrm{full}}_N$. Three maps are involved. First, `frickeInvolutionBar (1 * q)` is the $\overline{\mathbb{Q}}$-algebra automorphism of $\overline{F}_{1\cdot q}$ obtained by applying `geomAut` (base change of automorphisms along $\overline{\mathbb{Q}}\otimes_{\mathbb{Q}}-$) to `frickeInvolutionFull (1 * q)`, the chosen $\mathbb{Q}$-automorphism of $F^{\mathrm{full}}_{1\cdot q}$ satisfying `IsFrickeAutFull (1 * q)` when such an automorphism exists and the identity otherwise. Second, `heckeBetaBar (AlgebraicClosure ℚ) 1 q` is the $\overline{\mathbb{Q}}$-algebra homomorphism $\overline{F}_1 \to \overline{F}_{1\cdot q}$ induced by `qExpand`, the substitution multiplying all Laurent exponents by $q$, i.e. $\sum a_n t^n \mapsto \sum a_n t^{qn}$. Third, `heckeAlphaBar (AlgebraicClosure ℚ) 1 q` is the inclusion $\overline{F}_1 \hookrightarrow \overline{F}_{1\cdot q}$ coming from $1 \mid 1\cdot q$. The assertion is the equality of $\overline{\mathbb{Q}}$-algebra homomorphisms $\overline{F}_1 \to \overline{F}_{1\cdot q}$: `heckeBetaBar` followed by `frickeInvolutionBar (1 * q)` equals `heckeAlphaBar`.
--
--   This is the statement that the Fricke involution $w_q$ of the geometric function field of $X_0(q)$ interchanges the two degeneracy embeddings of the level-one field, here in the direction $w_q \circ \beta = \alpha$; no primality of $q$ is assumed. It is used in the analysis of prolongations of places from level one to level $q$, in particular in the construction of good representatives and tube equations for the cuspidal-class computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frickeInvolutionBar_comp_heckeBetaBar_one.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.frickeInvolutionBar_comp_heckeBetaBar_one (q : ℕ) [NeZero q] :
    (frickeInvolutionBar (1 * q)).toAlgHom.comp (heckeBetaBar (AlgebraicClosure ℚ) 1 q)
      = heckeAlphaBar (AlgebraicClosure ℚ) 1 q := by sorry
