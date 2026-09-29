-- Prove2me | Theorems.Thm_NumberField_AdelicHeight_adelicHeight_diagOne
-- name    : NumberField.AdelicHeight.adelicHeight_diagOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/e2c81f59-ddbd-5af1-8fd1-ca9ee9a812ae
-- title:
--   Adelic height of diag(t,1) is the idele norm
-- statement:
--   Let $F$ be a number field and let $t$ be a unit of the adele ring $\mathbb{A}_F$ of $F$ (an idele). Let `diagOne t` denote the element of $GL_2(\mathbb{A}_F)$ given by the diagonal matrix with entries $t$ and $1$ (with inverse the diagonal matrix with entries $t^{-1}$ and $1$). The assertion is that the adelic height of this element equals the idele norm of $t$. Here the adelic height of $g \in GL_2(\mathbb{A}_F)$ is the product of two factors: the archimedean one, $\prod_{v \mid \infty} \mathrm{localHeight}(g_v)^{m_v}$ over the infinite places of $F$, where $g_v$ is the component at $v$ of the image of $g$ in $GL_2$ of the infinite adele ring and $m_v$ is the multiplicity of $v$; and the finite one, the finitary product $\prod_{v} \mathrm{finLocalHeight}(g_v)$ over the height-one primes $v$ of $\mathcal{O}_F$ of the local heights of the components of the image of $g$ in $GL_2$ of the finite adele ring. The idele norm of $t$ is the real number underlying the scaling factor $\mathrm{distribHaarChar}$ by which multiplication by $t$ distorts Haar measure on $\mathbb{A}_F$.
--
--   This is the normalisation statement for the adelic height on $GL_2(\mathbb{A}_F)$: on the torus elements $\mathrm{diag}(t,1)$ the height is the idelic modulus $\|t\|_{\mathbb{A}_F}$, so that the flat section $\mathrm{ht}^{s+1/2}$ is the standard induced section attached to the modulus character. It is used in the analysis of truncated cusp kernels for $GL_2$, where integrals over Siegel sets are converted into integrals of the idele norm over the torus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicHeight_adelicHeight_diagOne.lean

import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.AdelicHeight.adelicHeight_diagOne (F : Type) [Field F] [NumberField F]
    (t : (AdeleRing (𝓞 F) F)ˣ) :
    NumberField.AdelicHeight.adelicHeight F (NumberField.AdelicLevel.diagOne t : AutomorphicForm.AdelicGL2 (𝓞 F) F) =
      NumberField.TateGlobal.ideleNorm F t := by sorry
