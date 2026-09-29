-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_form_casimir_eq_of_skew_archDeriv
-- name    : LanglandsTunnell.CubicInduction.form_casimir_eq_of_skew_archDeriv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/91d6b535-1aa9-5a2b-b1a2-d281b062fcbf
-- title:
--   Adjoints of the three mathfrakgl₃ central words under a skew hermitian form
-- statement:
--   Fix a $\mathbb C$-submodule $M$ of the space of complex-valued functions on $\mathrm{GL}_3(\mathbb A_{\mathbb Q})$, where $\mathbb A_{\mathbb Q}$ is the adele ring of $\mathbb Q$ formed from $\mathcal O_{\mathbb Q}$ and $\mathbb Q$. For $i,j \in \{0,1,2\}$ let $\partial_{ij}$ denote `WhittakerBlock.archDeriv i j`, the operator sending $\varphi$ to the function $g \mapsto \frac{d}{ds}\varphi\bigl(g\cdot \mathrm{archRealLift3}(I + s\,e_{ij})\bigr)\big|_{s=0}$, where $\mathrm{archRealLift3}$ lifts a real $3\times 3$ matrix to $\mathrm{GL}_3(\mathbb A_{\mathbb Q})$ when it is invertible (and to $1$ otherwise). Assume $M$ is stable under all nine $\partial_{ij}$, and let $B$ be a $\mathbb C$-valued function of two function arguments satisfying, on members of $M$: hermitian symmetry $B(w',w) = \overline{B(w,w')}$; linearity in the first argument, $B(zw_1+w_2,w') = zB(w_1,w')+B(w_2,w')$; and skewness of each $\partial_{ij}$, $B(\partial_{ij}w,w') = -B(w,\partial_{ij}w')$. Then for all $w,w' \in M$ the three conclusions hold: $B(C_1w,w') = -B(w,C_1w')$ for $C_1 = \sum_i \partial_{ii}$; $B(C_2w,w') = B(w,C_2w')$ for $C_2 = \sum_{i,j}\partial_{ij}\partial_{ji}$; and $B(C_3w,w') = -B\bigl(w, \sum_{i,j,k}\partial_{ij}\partial_{ki}\partial_{jk}w'\bigr)$ for $C_3 = \sum_{i,j,k}\partial_{ij}\partial_{jk}\partial_{ki}$, the last right-hand side being the reversed cubic word rather than $C_3$ itself.
--
--   This records the adjoints, with respect to a hermitian form whose archimedean right derivatives are skew, of the linear, quadratic and cubic central words in the nine operators $\partial_{ij}$ acting on a space of functions on $\mathrm{GL}_3(\mathbb A_{\mathbb Q})$: the linear word is skew, the quadratic one symmetric, and the cubic one is adjoint to minus the reversed cubic word. It is used in the analysis of the leading Whittaker coefficient module, via [`LanglandsTunnell.CubicInduction.leadingCoeff_eq_zero_or_exists_transitionStable_family_ne_bot_of_smoothingSubmodule_re`](thm.html#LanglandsTunnell.CubicInduction.leadingCoeff_eq_zero_or_exists_transitionStable_family_ne_bot_of_smoothingSubmodule_re), to constrain the spectral parameters of the relevant eigenfunctions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_form_casimir_eq_of_skew_archDeriv.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem
LanglandsTunnell.CubicInduction.form_casimir_eq_of_skew_archDeriv
    (M : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (h5 : ∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M)
    (B : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℂ)
    (hherm : ∀ w ∈ M, ∀ w' ∈ M, B w' w = (starRingEnd ℂ) (B w w'))
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ w' ∈ M, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hskew : ∀ w ∈ M, ∀ w' ∈ M, ∀ i j : Fin 3,
      B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w'))
    (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hw : w ∈ M) (w' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hw' : w' ∈ M) :
    B (WhittakerBlock.casimir1 w) w' = - B w (WhittakerBlock.casimir1 w') ∧
    B (WhittakerBlock.casimir2 w) w' = B w (WhittakerBlock.casimir2 w') ∧
    B (WhittakerBlock.casimir3 w) w' =
      - B w (fun g => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv k i (WhittakerBlock.archDeriv j k w')) g) := by sorry
