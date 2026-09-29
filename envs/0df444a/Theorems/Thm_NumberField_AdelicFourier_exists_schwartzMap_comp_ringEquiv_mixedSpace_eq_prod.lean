-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_exists_schwartzMap_comp_ringEquiv_mixedSpace_eq_prod
-- name    : NumberField.AdelicFourier.exists_schwartzMap_comp_ringEquiv_mixedSpace_eq_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/aa368d81-5572-566f-9c72-30e3f08a6a06
-- title:
--   Product bump functions on the infinite adeles
-- statement:
--   Let $F$ be a number field, and for each infinite place $w$ of $F$ let $t_w$ be a point of the completion $F_w$ and $U_w \subseteq F_w$ a set, assumed open and containing $t_w$. The assertion is the existence of a Schwartz function $g$ on the mixed space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ attached to the mixed embedding of $F$, with values in $\mathbb{C}$, together with a family of functions $g_w \colon F_w \to \mathbb{C}$ indexed by the infinite places, such that: for every element $x$ of the infinite adele ring $F_\infty$, the value of $g$ at the image of $x$ under the ring isomorphism $F_\infty \cong \mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ equals the finite product $\prod_w g_w(x_w)$; each $g_w$ is continuous; each $g_w$ has compact support; the topological support of each $g_w$ is contained in $U_w$; each value $g_w(y)$ has vanishing imaginary part and non-negative real part; and the real part of $g_w(t_w)$ is strictly positive at the prescribed point $t_w$.
--
--   This is the archimedean half of the construction of a factorisable non-negative test function: a smooth product bump on $F_\infty$ concentrated in prescribed neighbourhoods of prescribed points, of the kind used for the choice of test function in Tate-style local-global Fourier analysis. It is used in the construction of an element of the Schwartz–Bruhat space with prescribed factorisation behaviour and non-negative integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_exists_schwartzMap_comp_ringEquiv_mixedSpace_eq_prod.lean

import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace MeasureTheory
open scoped SchwartzMap
open scoped Classical in

theorem NumberField.AdelicFourier.exists_schwartzMap_comp_ringEquiv_mixedSpace_eq_prod
    (F : Type) [Field F] [NumberField F]
    (t : (w : InfinitePlace F) → w.Completion)
    (U : (w : InfinitePlace F) → Set w.Completion)
    (hU : ∀ w, IsOpen (U w)) (ht : ∀ w, t w ∈ U w) :
    ∃ (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (gw : (w : InfinitePlace F) → w.Completion → ℂ),
      (∀ x : InfiniteAdeleRing F, g (InfiniteAdeleRing.ringEquiv_mixedSpace F x) = ∏ w, gw w (x w)) ∧
      (∀ w, Continuous (gw w)) ∧ (∀ w, HasCompactSupport (gw w)) ∧ (∀ w, tsupport (gw w) ⊆ U w) ∧
      (∀ w y, (gw w y).im = 0 ∧ 0 ≤ (gw w y).re) ∧ (∀ w, 0 < (gw w (t w)).re) := by sorry
