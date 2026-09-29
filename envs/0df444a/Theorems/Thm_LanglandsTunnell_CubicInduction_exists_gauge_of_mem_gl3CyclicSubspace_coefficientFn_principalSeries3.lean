-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_gauge_of_mem_gl3CyclicSubspace_coefficientFn_principalSeries3
-- name    : LanglandsTunnell.CubicInduction.exists_gauge_of_mem_gl3CyclicSubspace_coefficientFn_principalSeries3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/7c7b6ec9-5b69-5721-b68d-b572e1b01c15
-- title:
--   Gauge majorant for cyclic translates of principal-series Whittaker coefficients
-- statement:
--   Let $p$ be a point of the height-one spectrum of $\mathcal O_{\mathbb Q}$, with completion $\mathbb Q_p :=$ `p.adicCompletion ℚ`, and let $\lambda = (\lambda_0,\lambda_1,\lambda_2)$ be a triple of group homomorphisms $\mathbb Q_p^\times \to \mathbb C^\times$, each locally constant, whose product $\lambda_0\lambda_1\lambda_2$ takes values of complex absolute value $1$ on every unit. Let `principalSeries3 p lam` be the $\mathbb C$-subspace of functions $f : \mathrm{GL}_3(\mathbb Q_p) \to \mathbb C$ that are locally constant, satisfy $f(u g) = f(g)$ for every upper unipotent $u =$ `upperUnipotent3 x y z`, and satisfy $f(\mathrm{diag}(a)g) = \bigl(\prod_i \lambda_i(a_i)\bigr)\,(\|a_0\|/\|a_2\|)\,f(g)$ for all $a \in (\mathbb Q_p^\times)^3$. Let $\Lambda$ be a $\mathbb C$-linear form on this space which is a Whittaker functional for the inverse of the local standard additive character `psiLocal ℚ p`, i.e. $\Lambda(F(\cdot\, u)) = \psi^{-1}(x+y)\,\Lambda(F)$ for $u =$ `upperUnipotent3 x y z`, let $f$ be an element of the principal series, and let $W : \mathrm{GL}_3(\mathbb Q_p) \to \mathbb C$ lie in the $\mathbb C$-span of the right translates $h \mapsto (\mathrm{coefficientFn}\ \Lambda\ f)(h g)$, $g \in \mathrm{GL}_3(\mathbb Q_p)$, of the coefficient function $g \mapsto \Lambda(f(\cdot\, g))$. Write, for $h \in \mathrm{GL}_3(\mathbb Q_p)$, $r(h)$ for the maximum of the norms of the three entries of the last row, $m(h)$ for the maximum of the norms of the three $2\times 2$ minors formed from the last two rows, $d(h) = \|\det h\|$, and set $X(h) = d(h)r(h)/m(h)^2$, $Y(h) = m(h)/r(h)^2$. Then there exist $B_g \in \mathbb R$, $t_g \in \mathbb N$ and $C_g \in \mathbb R$ such that for every $h$: if it is not the case that both $X(h) \le B_g$ and $Y(h) \le B_g$, then $W(h) = 0$; and if both $X(h) \le B_g$ and $Y(h) \le B_g$, then $\|W(h)\| \le C_g / (X(h)Y(h))^{t_g}$.
--
--   This is the gauge (two-regime majorant) estimate for Whittaker functions attached to a local principal series of $\mathrm{GL}_3(\mathbb Q_p)$: support in the region where the two mirabolic gauge quantities $X$ and $Y$ are bounded, with polynomial growth in $(XY)^{-1}$ there, and it is inherited by the whole cyclic space of right translates of a single Whittaker coefficient. It feeds the construction of gauge-majorised, congruence-invariant vectors used in the Rankin–Selberg and converse-theorem input to the Langlands–Tunnell argument, via [`LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_twist_coefficientFn_principalSeries3_congruenceK1_invariant_iotaGL_bump_of_pos_of_level`](thm.html#LanglandsTunnell.RankinSelberg.exists_mem_gl3CyclicSubspace_twist_coefficientFn_principalSeries3_congruenceK1_invariant_iotaGL_bump_of_pos_of_level); the proof cites the decomposition of a principal-series coefficient into finitely many translated Jacquet–Whittaker integrals of cell sections together with the vanishing and majorant estimates for those integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_gauge_of_mem_gl3CyclicSubspace_coefficientFn_principalSeries3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical

theorem LanglandsTunnell.CubicInduction.exists_gauge_of_mem_gl3CyclicSubspace_coefficientFn_principalSeries3
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i : Fin 3, IsLocallyConstant (lam i))
    (hωu : ∀ u : (p.adicCompletion ℚ)ˣ, ‖(((lam 0 * lam 1 * lam 2) u : ℂˣ) : ℂ)‖ = 1)
    (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ)
    (hΛ : IsWhittakerFunctional3 (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ Λ)
    (f : ↥(principalSeries3 p lam))
    (W : LocalGL3 p → ℂ) (hW : W ∈ gl3CyclicSubspace (coefficientFn Λ f)) :
    ∃ (Bg : ℝ) (tg : ℕ) (Cg : ℝ), ∀ h : LocalGL3 p,
      (¬ (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ Bg ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ Bg) → W h = 0) ∧
      (LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2 ≤ Bg ∧ LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2 ≤ Bg →
        ‖W h‖ ≤ Cg / ((LanglandsTunnell.CubicInduction.detSize h * LanglandsTunnell.CubicInduction.lastRowSup h / LanglandsTunnell.CubicInduction.minorSup h ^ 2) * (LanglandsTunnell.CubicInduction.minorSup h / LanglandsTunnell.CubicInduction.lastRowSup h ^ 2)) ^ tg) := by sorry
