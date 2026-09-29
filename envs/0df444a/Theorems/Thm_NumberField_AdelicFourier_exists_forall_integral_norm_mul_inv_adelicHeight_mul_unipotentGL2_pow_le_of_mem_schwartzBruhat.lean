-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_exists_forall_integral_norm_mul_inv_adelicHeight_mul_unipotentGL2_pow_le_of_mem_schwartzBruhat
-- name    : NumberField.AdelicFourier.exists_forall_integral_norm_mul_inv_adelicHeight_mul_unipotentGL2_pow_le_of_mem_schwartzBruhat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/e458ed87-7aa8-596b-b9bb-1655c13ea1d4
-- title:
--   Uniform polynomial height moments of Schwartz–Bruhat functions
-- statement:
--   Let $F$ be a number field, and equip the adele ring $\mathbb{A}_F$ of $\mathcal{O}_F$ in $F$ with a measurable space structure that is the Borel structure of its topology, together with an additive Haar measure $\mu$. Let $B \colon \mathbb{A}_F \to \mathbb{C}$ belong to `schwartzBruhat F`, the $\mathbb{C}$-submodule spanned by the pure tensors, i.e. by the functions $x \mapsto g(x_\infty)\,h(x_{\mathrm{f}})$ where $g$ is a Schwartz function on the mixed space of $F$ (evaluated on the infinite component of $x$ transported along the ring equivalence with the infinite adeles) and $h$ is a locally constant function with compact support on the finite adele ring. Let $C$ be a compact subset of $\mathrm{GL}_2(\mathbb{A}_F)$ and let $M$ be a natural number. Then there exists a real number $I$ such that for every $g \in C$ the function $$x \longmapsto \lVert B(x)\rVert \cdot \bigl(H(g\,n(x))^{-1}\bigr)^{M},\qquad n(x) = \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix},$$ is $\mu$-integrable and its integral over $\mathbb{A}_F$ is at most $I$. Here $H =$ `adelicHeight F` is the product of the archimedean height $\prod_{v \mid \infty} \mathrm{localHeight}(\cdot)^{\,\mathrm{mult}(v)}$ of the archimedean component of the matrix and the finite height $\prod^{\mathrm{f}}_{v} \mathrm{finLocalHeight}(\cdot)$ over the height one spectrum of $\mathcal{O}_F$ of its finite component, and the inverse is taken in $\mathbb{R}$ before raising to the $M$-th power. The bound $I$ is uniform in $g \in C$ but is not asserted to be positive.
--
--   This is the uniform polynomial-moment estimate for Schwartz–Bruhat functions on $\mathbb{A}_F$ tested against the inverse adelic height gauge along the unipotent orbit $x \mapsto g\,n(x)$, with the constant uniform over a compact family of base points $g$. The case $M = 0$ is the plain integrability statement [`NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat`](thm.html#NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat); the estimate is used in bounding unipotent averages of convolutions against powers of the idele norm in the analysis of automorphic forms on $\mathrm{GL}_2(\mathbb{A}_F)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_exists_forall_integral_norm_mul_inv_adelicHeight_mul_unipotentGL2_pow_le_of_mem_schwartzBruhat.lean

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

theorem NumberField.AdelicFourier.exists_forall_integral_norm_mul_inv_adelicHeight_mul_unipotentGL2_pow_le_of_mem_schwartzBruhat
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {B : AdeleRing (𝓞 F) F → ℂ} (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (M : ℕ) :
    ∃ I : ℝ, ∀ g ∈ C,
      Integrable (fun x : AdeleRing (𝓞 F) F => ‖B x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M) μ ∧
      ∫ x, ‖B x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M ∂μ ≤ I := by sorry
