-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg
-- name    : NumberField.AdelicFourier.exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/d9f041bc-5caa-58fb-8abd-d165a8173e10
-- title:
--   Schwartz–Bruhat function standard outside S with non-negative Fourier multiplier
-- statement:
--   Let $F$ be a number field, let $\psi$ be an additive character of $\mathbb{A}_F$ which is a global additive character in the sense of `IsGlobalAddChar` (trivial on the image of $F$, continuous, and not identically $1$), and let $S$ be a finite set of finite places of $F$. Assume $\psi$ is trivial on each local integer ring placed outside $S$: for every $v\notin S$ and every $r\in\mathcal{O}_v$, the adele with zero infinite part and finite part obtained by splicing $r$ into the $v$-coordinate of $0$ has $\psi$-value $1$. Let $a_0$ be an idele whose finite component at every $v\notin S$ equals $1$, and let $N$ be an open set of ideles containing $a_0$. Then there exist $B:\mathbb{A}_F\to\mathbb{C}$ and $\mu:\mathbb{A}_F^\times\to\mathbb{R}$ such that: $B$ lies in the Schwartz–Bruhat space, the $\mathbb{C}$-span of the pure tensors $x\mapsto g(x_\infty)h(x_{\mathrm{fin}})$ with $g$ a Schwartz function on the mixed space of $F$ and $h$ locally constant with compact support on $\mathbb{A}_{F,\mathrm{fin}}$; there are local functions $B_w$ on the completions at the infinite places and $B_v$ on the completions at the finite places with $B(x)$ equal, for all $x$, to the indicator of the set $\{x: x_v\in\mathcal{O}_v \text{ for all } v\notin S\}$ times $\big(\prod_w B_w(x_w)\big)\prod_{v\in S}B_v(x_v)$; for every idele $a$ one has $\int B(x)\,\psi(ax)\,dx=\mu(a)$ with respect to the additive Haar measure on $\mathbb{A}_F$ for the Borel structure; $\mu$ is Borel measurable on the ideles, non-negative, bounded above by some constant $M_0$; $\mu(a)=0$ whenever $a$ is fixed by the projection $\mathrm{partAt}_S$ (infinite part unchanged, finite part truncated to $S$) and $a\notin N$; and $\mu$ is integrable with $\int\mu\,d\nu_S>0$, where $\nu_S$ is the pushforward under $\mathrm{partAt}_S$ of the idelic Haar measure restricted to the subgroup of ideles that are units integrally outside $S$.
--
--   This is the adelic test-vector construction underlying the non-vanishing of a global zeta integral: the Fourier multiplier $a\mapsto\int B(x)\psi(ax)\,dx$ of a suitable Schwartz–Bruhat function is made non-negative, bounded, supported near a prescribed idele $a_0$ after projection to the $S$-part, and of positive total mass for the $S$-part measure. It is invoked in the proof that a unipotent average of a right convolution of the $S$-part zeta integrand is entire and not identically zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker

theorem NumberField.AdelicFourier.exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg
    (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hψS : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ r : v.adicCompletionIntegers F,
      ψ (@id (AdeleRing (𝓞 F) F) ((0 : InfiniteAdeleRing F),
        AdelicDock.splice (𝓞 F) F v 0 (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r))) = 1)
    (a₀ : (AdeleRing (𝓞 F) F)ˣ)
    (ha₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1)
    (N : Set (AdeleRing (𝓞 F) F)ˣ) (hN : IsOpen N) (ha₀N : a₀ ∈ N) :
    ∃ (B : AdeleRing (𝓞 F) F → ℂ) (μ : (AdeleRing (𝓞 F) F)ˣ → ℝ),
      B ∈ NumberField.AdelicFourier.schwartzBruhat F ∧
      (∃ (Bi : (w : InfinitePlace F) → w.Completion → ℂ) (Bf : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ),
        IsFactorizableStandardOutside B S Bi Bf) ∧
      (∀ a : (AdeleRing (𝓞 F) F)ˣ, (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * ψ (((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x) ∂(adelicAddHaar (𝓞 F) F)) = (μ a : ℂ)) ∧
      Measurable[NumberField.Idele.ideleBorel F] μ ∧ (∀ a, 0 ≤ μ a) ∧ (∃ M₀ : ℝ, ∀ a, μ a ≤ M₀) ∧
      (∀ a, NumberField.Idele.partAt F S a = a → a ∉ N → μ a = 0) ∧
      Integrable μ (NumberField.Idele.sPartMeasure F S) ∧ 0 < ∫ a, μ a ∂(NumberField.Idele.sPartMeasure F S) := by sorry
