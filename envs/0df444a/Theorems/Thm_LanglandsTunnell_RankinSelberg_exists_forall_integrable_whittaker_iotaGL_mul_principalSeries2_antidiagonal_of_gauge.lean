-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_whittaker_iotaGL_mul_principalSeries2_antidiagonal_of_gauge
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_whittaker_iotaGL_mul_principalSeries2_antidiagonal_of_gauge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/2147a9c7-8651-5aa3-a6bc-e4bc6fb7e7fe
-- title:
--   Convergence of the unfolded GL₃timesGL₂ local integral
-- statement:
--   Let $p$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ and write $F$ for the completion $\mathbb{Q}_p$ of $\mathbb{Q}$ at $p$. Let $W : \mathrm{GL}_3(F) \to \mathbb{C}$ be a function that is invariant under right translation by some open subgroup of $\mathrm{GL}_3(F)$ and satisfies a two-parameter gauge bound: setting $\alpha_1(h) = \lVert\det h\rVert \cdot r(h)/m(h)^2$ and $\alpha_2(h) = m(h)/r(h)^2$, where $r(h)$ is the maximum of the norms of the three entries of the last row of $h$ and $m(h)$ the maximum of the norms of the three $2\times 2$ minors $h_{1j}h_{2j'} - h_{1j'}h_{2j}$ formed from the last two rows, there are $B, C \in \mathbb{R}$ and $t \in \mathbb{N}$ such that $W(h) = 0$ whenever it fails that both $\alpha_1(h) \le B$ and $\alpha_2(h) \le B$, and $\lVert W(h)\rVert \le C/(\alpha_1(h)\alpha_2(h))^t$ whenever both do hold. Let $\chi_0, \chi_1 : F^\times \to \mathbb{C}^\times$ be multiplicative characters, each $\chi_i$ trivial on the set of units $u$ with $\lVert u\rVert_v = 1$ and (if $c_i \neq 0$) $v(u-1) \le \exp(-c_i)$, for given $c_0, c_1 \in \mathbb{N}$. Let $\varpi$ be a unit of valuation $\exp(-1)$ with $\lvert\chi_0(\varpi)\rvert < \lvert\chi_1(\varpi)\rvert$. Let $f : \mathrm{GL}_2(F) \to \mathbb{C}$ lie in the normalised principal series attached to $(\chi_0,\chi_1)$, that is, $f$ is locally constant, invariant under left translation by the upper unipotent matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and satisfies $f(\mathrm{diag}(a_0,a_1)g) = \chi_0(a_0)\chi_1(a_1)\sqrt{\lVert a_0\rVert/\lVert a_1\rVert}\, f(g)$; assume moreover $f$ invariant under right translation by some open subgroup. Let $w_0 \in \mathrm{GL}_2(F)$ have matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. Then, $\mathrm{GL}_2(F)$ being given its Borel $\sigma$-algebra, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$ there exists $\sigma_2 \in \mathbb{R}$ such that for every $s \in \mathbb{C}$ with $\operatorname{Re} s > \sigma_2$ the function $g \mapsto W(\iota(g))\, f(w_0 g)\, \lVert\det g\rVert^{\,s-1/2}$ is $\mu_2$-integrable, where $\iota(g) = \begin{pmatrix} g & 0\\ 0 & 1\end{pmatrix}$ and $\lVert\cdot\rVert$ is the module of $F$ given by the action on Haar measure.
--
--   This is the absolute-convergence input for the unfolding step in the local $\mathrm{GL}_3\times\mathrm{GL}_2$ Rankin–Selberg theory: after a $\mathrm{GL}_2$ Whittaker function is written as a Jacquet integral of a principal series section, the integral over $N\backslash\mathrm{GL}_2$ becomes the displayed integral over $\mathrm{GL}_2$, and the dominance condition $\lvert\chi_0(\varpi)\rvert < \lvert\chi_1(\varpi)\rvert$ together with the gauge bound on $W$ secures convergence in a right half-plane. It is used in establishing multiplicativity of the local functional equation in the $\mathrm{GL}_2$ variable and in the span computations for the local zeta integrals of the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_whittaker_iotaGL_mul_principalSeries2_antidiagonal_of_gauge.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_whittaker_iotaGL_mul_principalSeries2_antidiagonal_of_gauge
    (p : HeightOneSpectrum (𝓞 ℚ))
    (W : LocalGL3 p → ℂ)
    (hWsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g)
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (ϖ : (p.adicCompletion ℚ)ˣ) (hϖ : Valued.v (ϖ : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hdom : ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ < ‖((χ 1 ϖ : ℂˣ) : ℂ)‖)
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (hfsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), f (g * k) = f g)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∃ σ₂ : ℝ, ∀ s : ℂ, σ₂ < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (W (iotaGL g) * f (w₀ * g)) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
                (s - 1 / 2)) μ₂ := by sorry
