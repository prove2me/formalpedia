-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_indicator_unipotent_mul_localLevelOne_eq
-- name    : LanglandsTunnell.RankinSelberg.exists_pos_forall_rsLocalIntegral_indicator_unipotent_mul_localLevelOne_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/85984a03-40ce-51b1-9387-3618bfc65ebc
-- title:
--   Local big-cell Rankin–Selberg integral is a positive constant
-- statement:
--   Let $v$ be a nonzero prime of $\mathcal O_{\mathbb Q}$, and equip $\mathrm{GL}_2(\mathbb Q_v)$ (where $\mathbb Q_v$ is the $v$-adic completion) with the Borel $\sigma$-algebra of its topology. The assertion is: for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb Q_v)$ and every Haar measure $\mu_{N}$ on the subgroup $N$ obtained as the range of `unipotentGL2Hom`, i.e. the subgroup of matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ with $x \in \mathbb Q_v$, there is a real number $m > 0$ with the following two properties. Write $B$ for the set of products $n k$ with $n \in N$ and $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the preimage under the place-$v$ embedding [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) of the level-$\top$ subgroup `AdelicLevel.finiteLevelOne` of $\mathrm{GL}_2$ of the finite adèles (those adelic matrices for which both the matrix and its inverse satisfy `IsLevelOneMatrix` at the unit ideal), and let $\mathbf 1_B$ be its $\mathbb C$-valued indicator. First, for every $s \in \mathbb C$ the function $g \mapsto \mathbf 1_B(g)\,\mathbf 1_B(g)\,\bigl(\mathrm{modulus}(\det g)\bigr)^{s-1/2}$, with $\mathrm{modulus}$ the module of multiplication by a scalar on Haar measure on $\mathbb Q_v$ (zero at $0$), is integrable against $\mu_2$ weighted by the density [`HaarQuotient.density N μ_N`](def/HaarQuotient.html#L25), the normalisation $g \mapsto w(g)/\int_{N} w(xg)\,d\mu_N(x)$ of the auxiliary weight [`HaarQuotient.weight`](def/HaarQuotient.html#L12). Second, for every $s \in \mathbb C$ the value [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) of that integral, taken with $\delta(g) = \mathrm{modulus}(\det g)$ and with both arguments equal to $\mathbf 1_B$, equals $m$; in particular it is independent of $s$.
--
--   This is the local computation at a finite place of the volume of the big cell $N\cdot\mathrm{GL}_2(\mathcal O_v)$ in the quotient by the unipotent subgroup: since $|\det(nk)|_v = 1$ on the cell, the local Rankin–Selberg integral of the pair of big-cell indicators is a positive constant in $s$. It supplies the value of the local factors at the unramified reference places in `exists_ne_zero_forall_integrable_and_rsFinIntegral_indicator_eq_mul_finprod_rsLocalIntegral_of_pure_of_measurable`, where the finite adelic Rankin–Selberg integral is factorised over the places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsLocalIntegral_indicator_unipotent_mul_localLevelOne_eq.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_pos_forall_rsLocalIntegral_indicator_unipotent_mul_localLevelOne_eq
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
    ∃ m : ℝ, 0 < m ∧
      (∀ s : ℂ,
        Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
          ({x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}.indicator (fun _ => (1 : ℂ)) g *
            {x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}.indicator (fun _ => (1 : ℂ)) g) *
            ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂))) ∧
      ∀ s : ℂ,
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                v.adicCompletion ℚ) : ℝ))
            s
            ({x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}.indicator (fun _ => (1 : ℂ)))
            ({x : GL (Fin 2) (v.adicCompletion ℚ) | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, x = n * k}.indicator (fun _ => (1 : ℂ))) = m := by sorry
