-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice
-- name    : LanglandsTunnell.Converse.CuspSynthesis.exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/74f18d81-0bef-5c0e-b0b0-d7308ecc4938
-- title:
--   Estimates for the Whittaker series of a nice JL datum
-- statement:
--   Let $K$ be a number field, $\Pi$ a Hecke eigensystem over $K$ with complex coefficients (a non-zero level ideal together with families $a_v,b_v$ indexed by the finite places), $S$ a finite set of finite places, $\mathrm{archR}$, $\mathrm{archC}$ families of real and complex archimedean parameters at the real and complex places, $\varepsilon_S$ a family of characters of the local unit groups, and $\omega$ a character of the idele units that is admissible (trivial on principal ideles, continuous and unitary) and satisfies $\omega(\pi_v)=N(v)^{-1}\Pi.b_v$ for every $v\notin S$, where $\pi_v$ is the idele with uniformizer at $v$. Let $d$ be a $JL$ datum for $(S,\varepsilon_S,\omega)$, let $dR$, $dC$ be archimedean Whittaker data for the given parameters, let $dF$ be a finite Whittaker datum for $S$ and $\Pi$, and assume the predicate `IsJLNice` for $d$, the twist of $\Pi$ by $v\mapsto N(v)^{-1/2}$, and the archimedean parameters. Then seven assertions hold simultaneously. First, for every $g\in \mathrm{GL}_2(\mathbb{A}_K)$ the series `jlSeries'` attached to $d,dR,dC,dF$ equals $\sum'_{\alpha\in K^\times} d.a(\alpha)\,\varepsilon(g)\,W_\infty(\mathrm{diag}(\alpha,1)g)\,W_f(\mathrm{diag}(\alpha,1)g)$, with $\varepsilon=d.\mathrm{epsChar}$, $W_\infty=$ `archW'` and $W_f=dF.\mathrm{Wf}$, and $\mathrm{diag}(\alpha,1)$ taken via the global points. Second, there is a real $\kappa$ with $\|\Pi.a_v\|\le N(v)^\kappa$ and $\|\Pi.b_v\|\le N(v)^\kappa$ for all $v\notin S$. Third, $\|\varepsilon(g)\|\le 1$ for all $g$. Fourth, for every bounded family $\mathrm{coef}:K^\times\to\mathbb{C}$ vanishing at each $\alpha$ for which the valuation of $\alpha$ at some $v\in S$ exceeds $\exp$ of the level of the local additive character $\psi_v$, every continuous self-map $h$ of $\mathrm{GL}_2(\mathbb{A}_K)$ and every $g_0$, there are a neighbourhood $V$ of $g_0$ and a non-negative summable $b:K^\times\to\mathbb{R}$ such that $\|\mathrm{coef}(\alpha)\,\varepsilon(g)\,W_\infty(\mathrm{diag}(\alpha,1)h(g))\,W_f(\mathrm{diag}(\alpha,1)h(g))\|\le b(\alpha)$ for all $g\in V$ and all $\alpha$. Fifth, for all reals $c,u,d_1,d_2$ with $c>0$ and $d_1>0$ and every $x$, the function `jlSeries'` is bounded on the right translate by $x$ of the cut Siegel set `centreCutSiegelSet K c u d₁ d₂` (finite part integral, each archimedean local height at least $c$, each window $\mathrm{xWindowSq}$ at most $u^2$, each archimedean determinant norm in $[d_1,d_2]$); no positivity is required of $u$ or $d_2$. Sixth, `jlSeries'` is continuous on the set of $g$ satisfying `MemZK0At v (d.m v) g` for every $v\in S$. Seventh, `archW' archR archC dR dC` is continuous.
--
--   This is the package of analytic estimates underlying the construction of a cusp form from a nice $JL$ datum in the converse-theorem input to Langlands–Tunnell: eigenvalue growth, a locally uniform summable majorant for the Whittaker series, boundedness on translated Siegel sets, and continuity. It is used in the proofs that the translated sums are archimedean-holomorphic, satisfy the left transformation law under global points, and lie in $L^p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_CuspSynthesis_exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice.lean

import Definitions.Def_LanglandsTunnell_JLSynthesis
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_JLData
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel AutomorphicForm.WindowedSiegel
open LanglandsTunnell.Converse LanglandsTunnell.TateLocal NumberField.StandardAddChar
open Topology

theorem
LanglandsTunnell.Converse.CuspSynthesis.exists_growth_exponent_and_local_majorant_and_bounded_on_siegel_of_isJLNice
    (K : Type) [Field K] [NumberField K]
    (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (d : JLData K S epsS ω)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC) :
    (∀ g : AdelicGL2 (𝓞 K) K, jlSeries' d archR archC dR dC dF g =
      ∑' α : Kˣ, d.a α * d.epsChar g * archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * g)
        * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * g)) ∧
    (∃ κ : ℝ, ∀ v ∉ S,
        ‖Pi.a v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ ∧ ‖Pi.b v‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ κ) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, ‖d.epsChar g‖ ≤ 1) ∧
    (∀ coef : Kˣ → ℂ, (∃ C : ℝ, ∀ α, ‖coef α‖ ≤ C) →
      (∀ α : Kˣ, (∃ v : ↥S, ¬ Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
        ≤ WithZero.exp (addCharLevel (psiLocal K v.1))) → coef α = 0) →
      ∀ h : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K, Continuous h → ∀ g₀ : AdelicGL2 (𝓞 K) K,
        ∃ V ∈ 𝓝 g₀, ∃ b : Kˣ → ℝ, Summable b ∧ (∀ α, 0 ≤ b α) ∧ ∀ g ∈ V, ∀ α : Kˣ,
          ‖coef α * d.epsChar g * archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α) * h g)
            * dF.Wf (globalPoints (𝓞 K) K (diagOne α) * h g)‖ ≤ b α) ∧
    (∀ c u d₁ d₂ : ℝ, 0 < c → 0 < d₁ → ∀ x : AdelicGL2 (𝓞 K) K, ∃ C : ℝ,
      ∀ g ∈ (· * x) '' centreCutSiegelSet K c u d₁ d₂, ‖jlSeries' d archR archC dR dC dF g‖ ≤ C) ∧
    ContinuousOn (jlSeries' d archR archC dR dC dF) (kZeroSet S d.m) ∧
    Continuous (archW' archR archC dR dC) := by sorry
