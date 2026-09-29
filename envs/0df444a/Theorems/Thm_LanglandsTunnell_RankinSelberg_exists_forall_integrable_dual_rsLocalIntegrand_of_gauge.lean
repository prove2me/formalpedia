-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_dual_rsLocalIntegrand_of_gauge
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_dual_rsLocalIntegrand_of_gauge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/fe9e0ecd-7fbe-5613-aa1b-2114fe704c57
-- title:
--   Convergence of the dual local GL₃timesGL₂ Rankin–Selberg integrand
-- statement:
--   Let $v$ be a prime of $\mathcal{O}_{\mathbb{Q}}$, write $F = \mathbb{Q}_v$ for the completion, and let $\psi_v$ be an additive character of $F$ assumed equal to the inverse of the standard local character `psiLocal`. Let $W : \mathrm{GL}_3(F) \to \mathbb{C}$ satisfy $W(u(x,y,z)g) = \psi_v(x+y)W(g)$ for all upper unipotent $u(x,y,z)$, be right invariant under some open subgroup of $\mathrm{GL}_3(F)$, and be gauge-majorised: there are $B, C \in \mathbb{R}$ and $t \in \mathbb{N}$ such that, writing $\rho_1(h) = \|\det h\|\cdot r(h)/m(h)^2$ and $\rho_2(h) = m(h)/r(h)^2$ with $r(h)$ the maximum of the norms of the entries of the last row of $h$ and $m(h)$ the maximum of the norms of its three bottom $2\times 2$ minors, one has $W(h) = 0$ unless $\rho_1(h) \le B$ and $\rho_2(h) \le B$, and $\|W(h)\| \le C/(\rho_1(h)\rho_2(h))^t$ when both bounds hold. Let $\varpi$ be an element of the valuation ring with nonzero image of valuation $\exp(-1)$, let $b \in \mathbb{N}$, and let $W_2 : \mathrm{GL}_2(F) \to \mathbb{C}$ satisfy: $W_2\big(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\,g\big) = \psi^0_v(x)W_2(g)$ for the standard character $\psi^0_v$; right invariance under [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at level $v^b$, the pullback of the finite adelic level-one subgroup along the local embedding at $v$; $W_2(g\cdot t\,\mathrm{I}) = \omega_2(t)W_2(g)$ for a homomorphism $\omega_2 : F^\times \to \mathbb{C}^\times$; and shell growth: there are $C, A$ with $\|W_2(\mathrm{diag}(\varpi^m,1)k)\| \le C\,(\mathrm{N}v)^{Am}$ for all integers $m \ge 0$ and all $k$ in `localLevelOne` at level $\top$. Let $w_{0}$ be the element of $\mathrm{GL}_2(F)$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. Then, with $\mathrm{GL}_2(F)$ carrying its Borel structure, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$ and every Haar measure $\mu_N$ on the range of the homomorphism $x \mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$ there exists $\sigma_3 \in \mathbb{R}$ such that for every $s$ with $\sigma_3 < \operatorname{Re} s$ the function
--   $$g \mapsto \widetilde{W}(\iota(g))\cdot \|\det g\|\, W_2\big(w_{0}\,{}^{t}g^{-1}\big)\cdot \|\det g\|^{\,s-1/2},$$
--   where $\iota(g) = \mathrm{diag}(g,1)$, $\widetilde{W}(h) = W(w_3\,{}^{t}h^{-1})$ for the long Weyl element $w_3$ of $\mathrm{GL}_3$, and $\|\cdot\|$ denotes [`LanglandsTunnell.TateLocal.modulus`](def/LanglandsTunnell_TateLocalZeta.html#L15) (the module of multiplication by the determinant), is integrable for the measure $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent range with respect to $\mu_N$.
--
--   This is the absolute-convergence clause, on a right half-plane, for the dual local Rankin–Selberg integrand of a $\mathrm{GL}_3$ Whittaker function against a $\mathrm{GL}_2$ Whittaker partner at a finite place, the companion of the corresponding statement for the primal integrand. It feeds the local functional equation and the Laurent-type evaluation of the local integrals, being cited by the results identifying `rsLocalIntegral` and its dual on spans of Whittaker vectors and in the principal-series and shell-growth cases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_dual_rsLocalIntegrand_of_gauge.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AutomorphicForm_SmoothingKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_dual_rsLocalIntegrand_of_gauge
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
        C * (Ideal.absNorm v.asIdeal : ℝ) ^ (A * m))
    (w₀p : GL (Fin 2) (v.adicCompletion ℚ))
    (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
    ∃ σ₃ : ℝ,
        ∀ s : ℂ, σ₃ < s.re →
          Integrable
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (dualWhittakerFn3 W (iotaGL g) *
                  (((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                      v.adicCompletion ℚ) : ℝ) : ℂ) * W₂ (w₀p * transposeInvN (Fin 2) g))) *
                ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                    v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) := by sorry
