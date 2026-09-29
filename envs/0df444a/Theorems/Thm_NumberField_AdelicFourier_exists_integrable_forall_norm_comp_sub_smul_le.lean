-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_exists_integrable_forall_norm_comp_sub_smul_le
-- name    : NumberField.AdelicFourier.exists_integrable_forall_norm_comp_sub_smul_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/84a2b888-c697-5442-b350-ac861abc46e5
-- title:
--   Integrable domination of archimedean translates of a Schwartz–Bruhat function
-- statement:
--   Let $F$ be a number field, and equip its adele ring $\mathbb{A}_F$ with a Borel measurable structure compatible with its topology and with an additive Haar measure $\mu$. Let $B \colon \mathbb{A}_F \to \mathbb{C}$ lie in the Schwartz–Bruhat space [`NumberField.AdelicFourier.schwartzBruhat F`](def/NumberField_AdelicFourier.html#L80), that is, in the $\mathbb{C}$-linear span of the set of pure tensors: functions of the form $x \mapsto g(\iota(x_\infty))\, h(x_{\mathrm{f}})$, where $g$ is a Schwartz function on the mixed space $\prod_{v \text{ real}} \mathbb{R} \times \prod_{v \text{ complex}} \mathbb{C}$ of $F$, $\iota$ is the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace F` from the infinite adeles to that mixed space, and $h$ on the finite adeles $\mathbb{A}_{F,\mathrm{f}}$ is locally constant with compact support. Let $e$ be a vector of the mixed space. The assertion is that there exists $\mathrm{bound} \colon \mathbb{A}_F \to \mathbb{R}$, integrable with respect to $\mu$, such that for every adele $x$ and every real $t$ with $|t| < 1$ one has $\|B(x - (\iota^{-1}(t \cdot e),\, 0))\| \le \mathrm{bound}(x)$, the subtracted adele having archimedean component $\iota^{-1}(t\cdot e)$ and zero finite component.
--
--   This is the domination hypothesis needed to differentiate an adelic integral of a Schwartz–Bruhat function under the integral sign along a one-parameter archimedean translation: a single $\mu$-integrable majorant valid uniformly for $|t|<1$. It is used in the computation of Whittaker coefficients of unipotent averages, in [`AutomorphicForm.exists_mem_schwartzBruhat_whittakerCoefficient_unipotentAverage_diagOne_eq_trace_mul`](thm.html#AutomorphicForm.exists_mem_schwartzBruhat_whittakerCoefficient_unipotentAverage_diagOne_eq_trace_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_exists_integrable_forall_norm_comp_sub_smul_le.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicHaar MeasureTheory
open AutomorphicForm IsDedekindDomain NumberField.TateGlobal

theorem NumberField.AdelicFourier.exists_integrable_forall_norm_comp_sub_smul_le
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {B : AdeleRing (𝓞 F) F → ℂ} (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (e : mixedEmbedding.mixedSpace F) :
    ∃ bound : AdeleRing (𝓞 F) F → ℝ, Integrable bound μ ∧
      ∀ (x : AdeleRing (𝓞 F) F) (t : ℝ), t ∈ Metric.ball (0 : ℝ) 1 →
        ‖B (x - @id (AdeleRing (𝓞 F) F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • e), 0))‖ ≤ bound x := by sorry
