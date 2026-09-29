-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_exists_mem_schwartzBruhat_hasDerivAt_comp_sub_smul
-- name    : NumberField.AdelicFourier.exists_mem_schwartzBruhat_hasDerivAt_comp_sub_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/620f085d-7b28-5307-8b53-530895ba39a7
-- title:
--   Archimedean directional derivatives of Schwartz–Bruhat functions on A_F
-- statement:
--   Let $F$ be a number field and let $B : \mathbb{A}_F \to \mathbb{C}$ be a function on the adele ring of $F$ lying in [`NumberField.AdelicFourier.schwartzBruhat F`](def/NumberField_AdelicFourier.html#L80), that is, in the $\mathbb{C}$-linear span of the pure tensors: functions of the form $x \mapsto g\bigl(\text{ringEquiv\_mixedSpace}(x_\infty)\bigr)\, h(x_f)$, where $g$ is a Schwartz function on the mixed space $\prod_{v \text{ real}} \mathbb{R} \times \prod_{v \text{ complex}} \mathbb{C}$ of $F$, $h : \mathbb{A}_F^{\mathrm{fin}} \to \mathbb{C}$ is locally constant with compact support, and $x = (x_\infty, x_f)$ is the decomposition of an adele into its infinite and finite components, the infinite part being transported to the mixed space by the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace F`. Let $e$ be an element of the mixed space of $F$. Then there exists $B' : \mathbb{A}_F \to \mathbb{C}$, again in the same span, such that for every adele $x$ and every real $t$ the real function $s \mapsto B\bigl(x - (\text{ringEquiv\_mixedSpace}^{-1}(s \cdot e),\, 0)\bigr)$ is differentiable at $t$ with derivative exactly $B'\bigl(x - (\text{ringEquiv\_mixedSpace}^{-1}(t \cdot e),\, 0)\bigr)$; here the subtracted adele has trivial finite component. Thus a single Schwartz–Bruhat function $B'$, playing the role of $-\partial_e B$, computes the derivative of every archimedean translate simultaneously.
--
--   This is the statement that the Schwartz–Bruhat space on the adele ring of a number field is stable under differentiation in an archimedean direction, in the form needed for differentiating adelic translates. It is used in the analysis of Whittaker coefficients of unipotent averages, via [`AutomorphicForm.exists_mem_schwartzBruhat_whittakerCoefficient_unipotentAverage_diagOne_eq_trace_mul`](thm.html#AutomorphicForm.exists_mem_schwartzBruhat_whittakerCoefficient_unipotentAverage_diagOne_eq_trace_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_exists_mem_schwartzBruhat_hasDerivAt_comp_sub_smul.lean

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

theorem NumberField.AdelicFourier.exists_mem_schwartzBruhat_hasDerivAt_comp_sub_smul
    (F : Type) [Field F] [NumberField F]
    {B : AdeleRing (𝓞 F) F → ℂ} (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (e : mixedEmbedding.mixedSpace F) :
    ∃ B' : AdeleRing (𝓞 F) F → ℂ, B' ∈ NumberField.AdelicFourier.schwartzBruhat F ∧
      ∀ (x : AdeleRing (𝓞 F) F) (t : ℝ),
        HasDerivAt (fun s : ℝ => B (x - @id (AdeleRing (𝓞 F) F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (s • e), 0)))
          (B' (x - @id (AdeleRing (𝓞 F) F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • e), 0))) t := by sorry
