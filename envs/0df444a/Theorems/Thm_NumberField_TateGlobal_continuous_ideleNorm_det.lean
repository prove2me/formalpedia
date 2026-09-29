-- Prove2me | Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
-- name    : NumberField.TateGlobal.continuous_ideleNorm_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/78797bd5-f4f8-5eb2-9fb2-620164a10b0b
-- title:
--   Continuity of the idele norm of the determinant on adelic GL₂
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`. Write `AdelicGL2 (𝓞 F) F` for the general linear group of $2 \times 2$ matrices over $\mathbb{A}_F$, i.e. the unit group of the matrix ring $M_2(\mathbb{A}_F)$ with its induced topology, and for a unit $x \in \mathbb{A}_F^\times$ let `ideleNorm F x` be the real number obtained by casting to $\mathbb{R}$ the $\mathbb{R}_{\ge 0}$-valued distributive Haar character `distribHaarChar (AdeleRing (𝓞 F) F) x`, that is, the positive factor by which multiplication by $x$ scales an additive Haar measure of $\mathbb{A}_F$. The assertion is that the real-valued function on `AdelicGL2 (𝓞 F) F` sending $g$ to `ideleNorm F (Matrix.GeneralLinearGroup.det g)`, the idele norm of the determinant of $g$ viewed as a unit of $\mathbb{A}_F$, is continuous.
--
--   This is the continuity of the adelic modulus character $g \mapsto \|\det g\|_{\mathbb{A}}$ on $GL_2(\mathbb{A}_F)$, the normalising factor used throughout the adelic theory of automorphic forms on $GL_2$ to twist by powers of $\|\det\|$. It serves as a basic continuity input for the constructions of adelic zeta integrals and the cuspidal spectrum that invoke it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm_det.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm

theorem NumberField.TateGlobal.continuous_ideleNorm_det (F : Type) [Field F] [NumberField F] :
    Continuous fun g : AdelicGL2 (𝓞 F) F => ideleNorm F (Matrix.GeneralLinearGroup.det g) := by sorry
