-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_integral_indicator_forall_localAt_unipotent_mul_localLevelOne_withDensity_eq
-- name    : LanglandsTunnell.RankinSelberg.exists_pos_integral_indicator_forall_localAt_unipotent_mul_localLevelOne_withDensity_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/be9153b9-4632-52d0-874c-7fce2cd3b2e9
-- title:
--   Positivity of the finite-adelic big cell volume
-- statement:
--   Fix a Haar measure $\mu$ on `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean projection [`NumberField.AdelicLevel.glArch`](def/NumberField_AdelicLevel.html#L191) on $GL_2(\mathbb{A}_{\mathbb{Q}})$, and a Haar measure $\mu_N$ on [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43), the subgroup of that kernel cut out by `adelicUnipotent ℚ`, the image of [`AutomorphicForm.unipotentGL2Hom`](def/AutomorphicForm_ConstantTerm.html#L33) over the full adele ring; the adelic $GL_2$ carries the Borel $\sigma$-algebra of its topology and is assumed second countable. Let $A$ be the set of $g$ in `finiteAdelicGL2Subgroup ℚ` such that for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the local component `localAt ℚ v g` in $GL_2(\mathbb{Q}_v)$ can be written as $n\,k$ with $n$ in the range of [`AutomorphicForm.unipotentGL2Hom`](def/AutomorphicForm_ConstantTerm.html#L33) over `v.adicCompletion ℚ` (the upper unipotent matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, $x\in\mathbb{Q}_v$) and $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the pullback along the local embedding at $v$ of the finite-adelic level-one subgroup for the unit ideal. The assertion is that there is a real $V>0$ such that the $\mathbb{C}$-valued indicator of $A$ (value $1$ on $A$) is integrable for $\mu$ weighted by the quotient density [`HaarQuotient.density RSCarrier.finUnipotent μN`](def/HaarQuotient.html#L25), and its integral against that weighted measure equals $V$.
--
--   This records that the finite-adelic big cell $N_f\cdot GL_2(\widehat{\mathbb{Z}})$ has finite and strictly positive volume on the quotient $N_f\backslash GL_2(\mathbb{A}_{\mathbb{Q},f})$, the normalisation constant needed before the Whittaker-type integral of a pure vector can be broken up place by place. It is used in the Rankin–Selberg factorisation of such an integral into a finite product of local integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_pos_integral_indicator_forall_localAt_unipotent_mul_localLevelOne_withDensity_eq.lean

import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem LanglandsTunnell.RankinSelberg.exists_pos_integral_indicator_forall_localAt_unipotent_mul_localLevelOne_withDensity_eq
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure] :
    ∃ V : ℝ, 0 < V ∧
      Integrable
        ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ),
            ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun _ => (1 : ℂ)))
        (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) ∧
      (∫ g, {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ),
            ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun _ => (1 : ℂ)) g
          ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))) = (V : ℂ) := by sorry
