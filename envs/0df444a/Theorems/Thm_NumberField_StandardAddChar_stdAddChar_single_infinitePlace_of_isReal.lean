-- Prove2me | Theorems.Thm_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isReal
-- name    : NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/2116655b-6a98-5314-8e73-943b43bc3a00
-- title:
--   Standard adelic character on the line of a real place
-- statement:
--   Let $K$ be a number field, let $w$ be an infinite place of $K$ with $w$ real, and let $t \in \mathbb{R}$. Write $\mathbb{A}_K$ for the adele ring `AdeleRing (𝓞 K) K`, whose elements are pairs consisting of an archimedean component in the product of the completions $K_v$ over the infinite places and a finite component in the finite adeles. Consider the adele whose archimedean component is the function supported at $w$ with value $e^{-1}(t)$, where $e =$ `InfinitePlace.Completion.ringEquivRealOfIsReal hw` is the ring isomorphism $K_w \xrightarrow{\sim} \mathbb{R}$ attached to the real place $w$, and all other archimedean coordinates zero, and whose finite component is $0$. The assertion is that the standard additive character `stdAddChar K` of $\mathbb{A}_K$ — by definition the character $\psi_{\mathbb{Q}}$ pulled back along the adelic trace map of the trace data `adelicTraceData K` built from the finite trace homomorphism and the archimedean trace — takes at this adele the value $\exp(2\pi i t)$, the complex exponential of $2\pi i$ times the real number $t$.
--
--   This identifies the local component at a real place of the global standard additive character of $\mathbb{A}_K$ in the normalisation $\psi_K = \psi_{\mathbb{Q}} \circ \mathrm{Tr}_{\mathbb{A}_K/\mathbb{A}_{\mathbb{Q}}}$. It is used in the analytic theory of automorphic forms to convert the adelic transformation behaviour of Whittaker functionals under unipotents into the character $x \mapsto \exp(2\pi i x)$ along the real unipotent line at $w$, and is cited in the characterisation of `stdAddChar` by its values at infinite places and in the cuspidality and Whittaker coefficient estimates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isReal.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

open scoped Classical in

theorem NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (t : ℝ) :
    NumberField.StandardAddChar.stdAddChar K
        (show (AdeleRing (𝓞 K) K) from (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t), 0)) =
      Complex.exp (2 * Real.pi * Complex.I * t) := by sorry
