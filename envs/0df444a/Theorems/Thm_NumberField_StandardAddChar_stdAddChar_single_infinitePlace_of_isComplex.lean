-- Prove2me | Theorems.Thm_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isComplex
-- name    : NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/4adeace9-5fc8-5c98-bcf4-98043f898834
-- title:
--   Standard adelic character on the line of a complex place
-- statement:
--   Let $K$ be a number field, let $w$ be an infinite place of $K$ with `hw : w.IsComplex`, and let $z \in \mathbb{C}$. Write $e =$ `InfinitePlace.Completion.ringEquivComplexOfIsComplex hw` for the induced ring isomorphism $K_w \xrightarrow{\sim} \mathbb{C}$, and consider the adele of $K$ whose archimedean component is the function `Pi.single w (e.symm z)` (the value $e^{-1}(z)$ at the place $w$ and $0$ at every other infinite place) and whose finite component is $0$. The assertion is that the standard additive character `stdAddChar K` — by definition the character $\psi_{\mathbb{Q}}$ of the adeles of $\mathbb{Q}$ composed with the adelic trace homomorphism of the trace datum `adelicTraceData K`, which is assembled from the finite trace map `traceFinHom` together with its compatibility with the structure map and its continuity — takes at this adele the value $\exp\bigl(2\pi i \cdot (2\,\mathrm{Re}\, z)\bigr)$, the real number $2\,\mathrm{Re}\,z$ being coerced into $\mathbb{C}$.
--
--   This identifies the local component at a complex place of the standard additive character of $\mathbb{A}_K$, in the normalisation $\psi_K = \psi_{\mathbb{Q}} \circ \mathrm{Tr}$: the local trace of $\mathbb{C}/\mathbb{R}$ sends $z$ to $2\,\mathrm{Re}\,z$, so the value is independent of which of the two conjugate identifications $K_w \cong \mathbb{C}$ is used. It is the complex-place counterpart of the corresponding real-place formula, and is used in the treatment of Whittaker coefficients at complex places, where adelic unipotent covariance must be converted into an explicit exponential character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isComplex.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

open scoped Classical in

theorem NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isComplex
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex) (z : ℂ) :
    NumberField.StandardAddChar.stdAddChar K
        (show (AdeleRing (𝓞 K) K) from (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z), 0)) =
      Complex.exp (2 * Real.pi * Complex.I * ((2 * z.re : ℝ) : ℂ)) := by sorry
