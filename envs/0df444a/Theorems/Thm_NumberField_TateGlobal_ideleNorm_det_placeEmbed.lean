-- Prove2me | Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_placeEmbed
-- name    : NumberField.TateGlobal.ideleNorm_det_placeEmbed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/502ae031-816d-5b6a-9315-dffb145c7e51
-- title:
--   Idele norm of a determinant embedded at one finite place
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, and let $x$ be an element of $\mathrm{GL}_2$ over the $p$-adic completion $\mathbb{Q}_p =$ `p.adicCompletion ℚ`. Let `placeEmbed ℚ p` be the group homomorphism $\mathrm{GL}_2(\mathbb{Q}_p) \to \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ obtained by composing `localEmbed`, which sends a matrix to the finite-adelic matrix whose $p$-component is the given matrix and whose component at every other finite place is the identity, with `finEmbed`, which sends a finite-adelic matrix to the adelic matrix with that finite part and identity archimedean part. The assertion is the equality of two real numbers: on the left, `ideleNorm ℚ` of the determinant of `placeEmbed ℚ p x`, that is the real value of the distributive Haar character `distribHaarChar` of the adele ring of $\mathbb{Q}$ evaluated at that unit; on the right, the real cast of [`LanglandsTunnell.TateLocal.modulus`](def/LanglandsTunnell_TateLocalZeta.html#L15) of the underlying element of $\mathbb{Q}_p$ of the determinant of $x$, where `modulus a` is $0$ for $a = 0$ and otherwise the distributive Haar character of $\mathbb{Q}_p$ at the unit determined by $a$.
--
--   This is the one-place case of Tate's description of the idele module as the product of the local moduli: the adelic Haar module of an idele supported at a single finite place is the local modulus there. It is used to match the character $\lVert\det\rVert^{s}$ of a finite-adelic Rankin–Selberg carrier with the local character $\lvert\det\rvert_p^{s}$ when one local factor is isolated, and is cited in the Rankin–Selberg and converse-theorem parts of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_ideleNorm_det_placeEmbed.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField UnramifiedWhittaker

theorem NumberField.TateGlobal.ideleNorm_det_placeEmbed (p : HeightOneSpectrum (𝓞 ℚ))
    (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ p x)) =
      (LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det x : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) := by sorry
