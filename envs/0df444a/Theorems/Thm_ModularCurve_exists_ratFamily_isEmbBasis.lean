-- Prove2me | Theorems.Thm_ModularCurve_exists_ratFamily_isEmbBasis
-- name    : ModularCurve.exists_ratFamily_isEmbBasis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/4bf1f2ce-daae-5b7a-b5d2-49d487dd3e41
-- title:
--   Embedding basis of X₀(p) with rational q-expansions
-- statement:
--   Let $p$ be a prime and $r$ a natural number. Write $F^{\mathrm{full}}_{1\cdot p} =$ `modularFunctionFieldFull (1 * p)` for the subfield of the Laurent series field $\mathbb{Q}(\!(q)\!)$ generated over $\mathbb{Q}$ by the expansions $\mathrm{qExpand}\ \mathbb{Q}\ d\ j_q$ for the nonzero divisors $d$ of $1\cdot p$, and $\bar F_{1\cdot p} =$ `modularFunctionFieldBar (1 * p)` for the subfield of $\bar{\mathbb{Q}}(\!(q)\!)$ generated over $\bar{\mathbb{Q}}$ by the coefficientwise images $\mathrm{coeffEmb}(x)$, $x \in F^{\mathrm{full}}_{1\cdot p}$, where $\bar{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Call a family $s : \mathrm{Fin}\ r \to \bar F_{1\cdot p}$ an embedding basis when it is linearly independent over $\bar{\mathbb{Q}}$ and its range spans the Riemann–Roch space of the divisor $\mathrm{embDegree}(1\cdot p)\cdot \bar\infty$ (the functions $f$ with $v(f) \le \exp(D(v))$ at every place $v$ of $\bar F_{1\cdot p}$ over $\bar{\mathbb{Q}}$, where $\bar\infty = \mathrm{cuspInftyBar}(1\cdot p)$). Given such an $s$, the theorem asserts the existence of a family $g : \mathrm{Fin}\ r \to F^{\mathrm{full}}_{1\cdot p}$ whose coefficientwise base change, $l \mapsto \mathrm{coeffEmb}_{\bar{\mathbb{Q}}}(g_l)$ viewed inside $\bar F_{1\cdot p}$, is again an embedding basis. Thus the hypothesis on $s$ is used only through the resulting dimension count $r$.
--
--   This is the Galois-descent statement that the Riemann–Roch space of the multiple $\mathrm{embDegree}(1\cdot p)\cdot\bar\infty$ of the cusp on $X_0(p)$ is defined over $\mathbb{Q}$: an arbitrary $\bar{\mathbb{Q}}$-basis of that space may be replaced by one consisting of functions with rational $q$-expansions. It supplies the rational families used in the construction of the projective embedding data, being cited by [`ModularCurve.MultCovering.exists_famCtx`](thm.html#ModularCurve.MultCovering.exists_famCtx) and [`ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue`](thm.html#ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ratFamily_isEmbBasis.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_ratFamily_isEmbBasis (p : ℕ) [Fact p.Prime] {r : ℕ}
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    ∃ g : Fin r → ↥(modularFunctionFieldFull (1 * p)),
      IsEmbBasis (1 * p) (fun l => (⟨coeffEmb (AlgebraicClosure ℚ) ((g l : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (g l).2⟩ : ↥(modularFunctionFieldBar (1 * p)))) := by sorry
