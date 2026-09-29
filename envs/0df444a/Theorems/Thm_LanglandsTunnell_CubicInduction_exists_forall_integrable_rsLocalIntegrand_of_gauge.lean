-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_integrable_rsLocalIntegrand_of_gauge
-- name    : LanglandsTunnell.CubicInduction.exists_forall_integrable_rsLocalIntegrand_of_gauge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/a71ed9b5-e85d-5870-9067-6669435c177f
-- title:
--   Convergence of the local GL₃timesGL₂ Rankin–Selberg integral
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, and let $\psi_v$ be an additive character of the completion $\mathbb{Q}_v$ with values in $\mathbb{C}$ which is assumed to be the inverse of the standard local character [`NumberField.StandardAddChar.psiLocal ℚ v`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) (the standard adelic character composed with the embedding of $\mathbb{Q}_v$ at $v$). Let $W$ be a $\mathbb{C}$-valued function on $\mathrm{GL}_3(\mathbb{Q}_v)$ satisfying $W(u(x,y,z)g)=\psi_v(x+y)W(g)$ for all $x,y,z\in\mathbb{Q}_v$ and all $g$, where $u(x,y,z)$ is the upper unipotent matrix `upperUnipotent3 x y z`; assume $W$ is right invariant under some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$, and gauge majorised: there are $B,C\in\mathbb{R}$ and $t\in\mathbb{N}$ such that, writing $d(h)=\lVert\det h\rVert$, $\ell(h)$ for the maximum of the norms of the three entries of the last row of $h$, and $m(h)$ for the maximum of the norms of the three bottom $2\times 2$ minors `bottomMinor h 0 1`, `bottomMinor h 0 2`, `bottomMinor h 1 2`, one has $W(h)=0$ whenever the two conditions $d(h)\ell(h)/m(h)^2\le B$ and $m(h)/\ell(h)^2\le B$ do not both hold, while if both hold then $\lVert W(h)\rVert\le C\big/\big((d(h)\ell(h)/m(h)^2)\,(m(h)/\ell(h)^2)\big)^t$. Let $\varpi$ be an element of the valuation ring of $\mathbb{Q}_v$ whose image in $\mathbb{Q}_v$ is non-zero of valuation $\exp(-1)$, i.e. a uniformiser, and let $b\in\mathbb{N}$. Let $W_2:\mathrm{GL}_2(\mathbb{Q}_v)\to\mathbb{C}$ satisfy: $W_2\big(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\, g\big)=\psi_{v,\mathrm{std}}(x)W_2(g)$ for the standard character $\psi_{v,\mathrm{std}}=$ `psiLocal ℚ v`; right invariance under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b)`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding $\mathrm{GL}_2(\mathbb{Q}_v)\to\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}})$ of the finite level-one subgroup of level $v^b$; a central transformation law $W_2(g\cdot t\,I_2)=\omega_2(t)W_2(g)$ for a homomorphism $\omega_2:\mathbb{Q}_v^\times\to\mathbb{C}^\times$; and shell growth: there are $C,A\in\mathbb{R}$ with $\lVert W_2(\mathrm{diag}(\varpi^{m},1)k)\rVert\le C\,(\mathrm{N}v)^{A m}$ for all integers $m\ge 0$ and all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), where $\mathrm{N}v$ is the absolute norm of $v$. The conclusion is that for every $g_3\in\mathrm{GL}_3(\mathbb{Q}_v)$, every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_v)$ (with its Borel structure) and every Haar measure $\mu_N$ on the image of the homomorphism $x\mapsto\big(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\big)$, there exists $\sigma_2\in\mathbb{R}$ such that for every $s\in\mathbb{C}$ with $\mathrm{Re}\,s>\sigma_2$ the function $g\mapsto W(\iota(g)g_3)\,W_2(g)\,\mathrm{mod}(\det g)^{s-1/2}$, with $\iota$ the block embedding $\mathrm{GL}_2\hookrightarrow\mathrm{GL}_3$ and $\mathrm{mod}$ the local modulus (the distributive Haar character, equal to the normalised absolute value), is integrable against $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent subgroup relative to $\mu_N$.
--
--   This is the non-archimedean convergence statement for the local Rankin–Selberg integral of a $\mathrm{GL}_3$ Whittaker function against a $\mathrm{GL}_2$ one, in the form needed for the local zeta integrals of the cubic-induction construction: a right half-plane of absolute convergence depending only on the gauge data of $W$ and on the level and shell growth of $W_2$. It feeds the statements about the local Rankin–Selberg integrals on spans of translates, their functional equations and their Laurent expansions in the Rankin–Selberg module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_integrable_rsLocalIntegrand_of_gauge.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse
open scoped nonZeroDivisors
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.exists_forall_integrable_rsLocalIntegrand_of_gauge
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ)
    (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
    (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) → W₂ (g * k) = W₂ g)
    (ω₂ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hW₂Z : ∀ (t : (v.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ((ω₂ t : ℂˣ) : ℂ) * W₂ g)
    (hW₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
      ‖W₂ (UnramifiedWhittaker.diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C * (Ideal.absNorm v.asIdeal : ℝ) ^ (A * m)) :
    ∀ g₃ : LocalGL3 v,
      letI := localGLBorel ℚ v
      haveI := borelSpace_localGLBorel ℚ v
      ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
      ∃ σ₂ : ℝ,
          ∀ s : ℂ, σ₂ < s.re →
            Integrable
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (W (iotaGL g * g₃) * W₂ g) *
                  ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                      v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) := by sorry
