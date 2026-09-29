-- Prove2me | Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
-- name    : NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/77fc03f1-000a-5b50-902b-3bfec19fc4ec
-- title:
--   Bounded distortion of the adelic height by compact right translation
-- statement:
--   Let $F$ be a number field and let $C$ be a compact subset of $\mathrm{GL}_2$ over the adele ring of $F$, that is of `AdelicGL2 (𝓞 F) F`, the general linear group of $2\times 2$ matrices over `AdeleRing (𝓞 F) F`. The assertion is the existence of two real numbers $\kappa$ and $K$ with $\kappa > 0$ such that for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ and every $x \in C$ one has both $\kappa \cdot \mathrm{adelicHeight}_F(g) \le \mathrm{adelicHeight}_F(g x)$ and $\mathrm{adelicHeight}_F(g x) \le K \cdot \mathrm{adelicHeight}_F(g)$. Here `adelicHeight F g` is the product of an archimedean and a non-archimedean factor: the archimedean factor is $\prod_{v} \mathrm{localHeight}(g_v)^{m_v}$, the product over the infinite places $v$ of $F$ of the local height of the component at $v$ of the image of $g$ under the map `glArch` induced by the projection of the adeles to the infinite adeles, raised to the power of the multiplicity $m_v$ of $v$; the non-archimedean factor is the finite product, over the height-one primes $v$ of $\mathcal{O}_F$, of the values `finLocalHeight` of the component at $v$ of the image of $g$ under the corresponding map `glFin` to $\mathrm{GL}_2$ of the finite adeles. Thus the constants are uniform in both $g$ and $x$; positivity is asserted for $\kappa$ only.
--
--   This is the statement that right translation by a fixed compact set distorts the adelic height on $\mathrm{GL}_2(\mathbb{A}_F)$ only by bounded multiplicative factors, the basic uniformity used in reduction theory for $\mathrm{GL}_2$ over a number field. It is invoked throughout the treatment of windowed Siegel sets and Siegel coverings, for instance in the height bounds for pseudo-Eisenstein functions and in the construction of convolution operators attached to slab profiles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact.lean

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

theorem NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) :
    ∃ κ K : ℝ, 0 < κ ∧ ∀ (g : AdelicGL2 (𝓞 F) F), ∀ x ∈ C,
      κ * adelicHeight F g ≤ adelicHeight F (g * x) ∧ adelicHeight F (g * x) ≤ K * adelicHeight F g := by sorry
