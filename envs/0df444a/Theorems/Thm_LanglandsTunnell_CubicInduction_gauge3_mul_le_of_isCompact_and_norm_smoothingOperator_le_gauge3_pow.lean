-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow
-- name    : LanglandsTunnell.CubicInduction.gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/6b235d9a-713e-5111-a3f2-245e0a4b0927
-- title:
--   Gauge bounds: right compact translation and smoothing on GL₃(A_ℚ)
-- statement:
--   The theorem is a closed statement: a conjunction of two assertions about the group $G =$ `AdelicGL 3 (𝓞 ℚ) ℚ` of units of $3\times 3$ matrices over the adele ring of $\mathbb{Q}$, both formulated with the gauge `gauge3 ℚ`, which sends $g$ to $\max(1, \mathrm{archGauge}_3(g)\cdot \mathrm{finGauge}_3(g))$, where $\mathrm{archGauge}_3(g) = 1 + \sum_{w} \mathtt{matrixSize}$ of the archimedean component of $g$ at the infinite place $w$, and $\mathrm{finGauge}_3(g)$ is the finitely supported product over the height-one primes $v$ of $\mathcal{O}_{\mathbb{Q}}$ of the nonnegative real `matrixSupSize` of the component of $g$ at $v$. First: for every compact subset $K \subseteq G$ there is a real constant $C$ such that $\mathrm{gauge}_3(gk) \le C\,\mathrm{gauge}_3(g)$ for all $k \in K$ and all $g \in G$. Second: for every natural number $N$ and all functions $f, \varphi \colon G \to \mathbb{C}$ such that (i) there is a real $C$ with $\|f(g)\| \le C\,\mathrm{gauge}_3(g)^N$ for all $g$, and (ii) $\varphi$ is a smoothing kernel, i.e. there are $\alpha \colon (\mathrm{Fin}\,3 \to \mathrm{Fin}\,3 \to \mathbb{R}) \to \mathbb{C}$ which is $C^\infty$, has compact support and has $\operatorname{tsupport}\alpha$ contained in the set of matrices of nonzero determinant, together with subgroups $K'_p \subseteq \mathrm{GL}_3(\mathbb{Q}_p)$ for each height-one prime $p$ that are all open and compact and satisfy $K'_p = \mathtt{localMaximalCompact3}$ (the matrices all of whose entries, and all of whose inverse's entries, have valuation $\le 1$) for cofinitely many $p$, such that $\varphi(g) = \alpha(\mathrm{archEntries}\,g)$ times the indicator at $g$ of $\{x : \forall p,\ x_p \in K'_p\}$, where $\mathrm{archEntries}\,g$ records the real coordinate of the archimedean part of each entry of $g$ — there is a real constant $C'$ with $\|(\mathtt{smoothingOperator}\,\varphi\,f)(g)\| \le C'\,\mathrm{gauge}_3(g)^N$ for all $g \in G$, where $(\mathtt{smoothingOperator}\,\varphi\,f)(x) = \int_G \varphi(g) f(xg)\,dg$ against the Haar measure `adelicGLHaar` on $G$. Note that the exponent $N$ in the conclusion is the same as in the hypothesis.
--
--   These are the two growth-bookkeeping facts used to keep moderate-growth bounds stable in the slab $L^2$ theory on $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$: the gauge is quasi-invariant under right translation by a compact set, and convolution with a compactly supported smooth-times-locally-constant kernel preserves a bound by a fixed power of the gauge. They are invoked in the estimates for the smoothing operator on functions with prescribed idele-norm determinant, in the Siegel-type growth bound for cuspidal functions, and in the construction of the seed package from archimedean derivative translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.gauge3_mul_le_of_isCompact_and_norm_smoothingOperator_le_gauge3_pow :
    (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K →
      ∃ C : ℝ, ∀ k ∈ K, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, gauge3 ℚ (g * k) ≤ C * gauge3 ℚ g) ∧
    ∀ (N : ℕ) (f φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ‖f g‖ ≤ C * gauge3 ℚ g ^ N) → SlabL2.IsSmoothingKernel φ →
        ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ‖SlabL2.smoothingOperator φ f g‖ ≤ C * gauge3 ℚ g ^ N := by sorry
