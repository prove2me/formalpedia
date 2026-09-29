-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed
-- name    : LanglandsTunnell.RankinSelberg.exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/0288f1cf-2217-5a43-9e49-654613c256a7
-- title:
--   One-place disintegration of a finite-adelic unipotent quotient integral
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$ (a finite place), and assume $GL_2$ of the adele ring of $\mathbb{Q}$, with its Borel structure coming from the topology, is second countable. Let $\mu$ be a Haar measure on `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean-component homomorphism `AdelicLevel.glArch` on $GL_2(\mathbb{A}_\mathbb{Q})$, and let $\mu_N$ be a Haar measure on [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43), the adelic unipotent subgroup `adelicUnipotent ℚ` viewed as a subgroup of that kernel. Equip $GL_2$ of the completion $\mathbb{Q}_v$ with its Borel structure. Then for every Haar measure $\mu_v$ on $GL_2(\mathbb{Q}_v)$ and every Haar measure $\mu_{N,v}$ on the range of `unipotentGL2Hom`, i.e. the image of $(\mathbb{Q}_v,+)$ under $x \mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$, there exists a measure $\mu'$ on `finiteAdelicGL2Subgroup ℚ` such that: $\mu'$ is s-finite; for $\mu'$-almost every $g'$ the $v$-component `localAt ℚ v g'` equals $1$; and for every measurable $\Phi$ from `finiteAdelicGL2Subgroup ℚ` to $[0,\infty]$ satisfying $\Phi(ng) = \Phi(g)$ for all $n$ in [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43), one has $$\int \Phi \, d\bigl(\mu\text{ with density } \rho_{N}\bigr) = \int\!\!\int \Phi\bigl(g' \cdot \mathrm{finFactor}(\iota_v(x))\bigr)\, d\bigl(\mu_v \text{ with density } \rho_{N,v}\bigr)(x)\, d\mu'(g'),$$ where $\rho_N =$ [`HaarQuotient.density RSCarrier.finUnipotent μN`](def/HaarQuotient.html#L25) and $\rho_{N,v}$ is the corresponding density for the local unipotent subgroup and $\mu_{N,v}$ (each being a value of the project's `weight` function divided by its integral along the relevant coset), $\iota_v =$ [`UnramifiedWhittaker.placeEmbed ℚ v`](def/UnramifiedWhittaker_HeckeRecursion.html#L47) places $x$ at $v$ and $1$ elsewhere, and [`RSCarrier.finFactor`](def/LanglandsTunnell_RSCarrierSplit.html#L17) divides out the archimedean component so as to land in `finiteAdelicGL2Subgroup ℚ`. Both sides may be infinite.
--
--   This is the measure-theoretic disintegration used to split off a single finite place in the Rankin–Selberg computation: the Haar measure on the finite-adelic group, weighted by the unipotent quotient density, is written as an integral over a prime-to-$v$ parameter of the corresponding local weighted integral at $v$. It is cited in the factorisation of the finite-adelic Rankin–Selberg integral into an Euler product of local integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed.lean

import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_RSCarrierSplit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped ENNReal in

theorem LanglandsTunnell.RankinSelberg.exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (v : HeightOneSpectrum (𝓞 ℚ))
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure] :
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μv : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μv.IsHaarMeasure]
      (μNv : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μNv.IsHaarMeasure],
    ∃ μ' : Measure (finiteAdelicGL2Subgroup ℚ), SFinite μ' ∧
      (∀ᵐ g' : finiteAdelicGL2Subgroup ℚ ∂μ', localAt ℚ v (g' : AdelicGL2 (𝓞 ℚ) ℚ) = 1) ∧
      ∀ Φ : finiteAdelicGL2Subgroup ℚ → ℝ≥0∞, Measurable Φ →
        (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ), Φ ((n : finiteAdelicGL2Subgroup ℚ) * g) = Φ g) →
        ∫⁻ g, Φ g ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) =
          ∫⁻ g', ∫⁻ x, Φ (g' * RSCarrier.finFactor (UnramifiedWhittaker.placeEmbed ℚ v x))
              ∂(μv.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv))
            ∂μ' := by sorry
