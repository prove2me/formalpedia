-- Prove2me | Theorems.Thm_NumberField_AdelicHeight_adelicHeight_diagOne_mul
-- name    : NumberField.AdelicHeight.adelicHeight_diagOne_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/7d104a1b-849f-54fa-8d1d-b8c8c5c94930
-- title:
--   Adelic height scales by the idelic norm under diag(a,1)
-- statement:
--   Let $F$ be a number field (a field with a `NumberField` instance), let $a$ be a unit of the adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`, and let $h$ be an element of `AdelicGL2 (𝓞 F) F`, that is, of $\mathrm{GL}_2(\mathbb{A}_F)$ in the sense of `Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 F) F)`. Write `diagOne a` for the image of $a$ under the monoid homomorphism sending a unit to the invertible diagonal matrix $\mathrm{diag}(a,1)$, with inverse $\mathrm{diag}(a^{-1},1)$. The height in question is `adelicHeight F g`, defined as the product of the archimedean height `archHeight F (glArch (𝓞 F) F g)`, itself the product over the infinite places $w$ of $F$ of `localHeight` of the component of $g$ at $w$ raised to the power $w.\mathrm{mult}$, with the finite height `finHeight F (glFin (𝓞 F) F g)`, itself the multiplicative finprod over the height-one primes $v$ of $\mathcal{O}_F$ of `finLocalHeight` of the component of $g$ at $v$; here `glArch` and `glFin` are the maps on $\mathrm{GL}_2$ induced by the projections of $\mathbb{A}_F$ to the infinite and to the finite adeles. The assertion is the identity $$\mathrm{adelicHeight}_F(\mathrm{diag}(a,1)\,h) = \|a\|\cdot \mathrm{adelicHeight}_F(h),$$ where $\|a\| =$ `ideleNorm F a` is the real number underlying the distributive Haar character `distribHaarChar (AdeleRing (𝓞 F) F) a` of multiplication by $a$ on $\mathbb{A}_F$.
--
--   This is the homogeneity of the adelic height on $\mathrm{GL}_2(\mathbb{A}_F)$ under left multiplication by the torus element $\mathrm{diag}(a,1)$: the height is multiplied by the module $\|a\|_{\mathbb{A}}$ of the idele $a$. It is used in the analysis of windowed Siegel sets and pseudo-Eisenstein approximation, where height bounds must be transported along the torus direction, for instance in the approximation statements for invariant band-supported functions and in the norm estimates for right convolution by $\mathrm{diag}(a,1)$ times a unipotent element.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicHeight_adelicHeight_diagOne_mul.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal NumberField.AdelicHeight

theorem NumberField.AdelicHeight.adelicHeight_diagOne_mul
    (F : Type) [Field F] [NumberField F] (a : (AdeleRing (𝓞 F) F)ˣ) (h : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (diagOne a * h) = ideleNorm F a * adelicHeight F h := by sorry
