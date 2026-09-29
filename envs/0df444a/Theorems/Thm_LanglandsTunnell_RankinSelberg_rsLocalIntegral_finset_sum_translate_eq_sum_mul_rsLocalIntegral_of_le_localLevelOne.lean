-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_rsLocalIntegral_finset_sum_translate_eq_sum_mul_rsLocalIntegral_of_le_localLevelOne
-- name    : LanglandsTunnell.RankinSelberg.rsLocalIntegral_finset_sum_translate_eq_sum_mul_rsLocalIntegral_of_le_localLevelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/050d90df-9177-5ad9-831c-58a423324764
-- title:
--   Translating the first factor of a local Rankin–Selberg integral
-- statement:
--   Fix a height-one prime $p$ of $\mathcal{O}_{\mathbb{Q}}$, write $F$ for the completion $\mathbb{Q}_p$, and let $\theta$ be an additive character of $F$ with values in $\mathbb{C}$. Let $A,B\colon \mathrm{GL}_2(F)\to\mathbb{C}$ be continuous and satisfy, for $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, the transformation laws $A(n(x)g)=\theta^{-1}(x)A(g)$ and $B(n(x)g)=\theta(x)B(g)$ for all $x\in F$ and $g\in\mathrm{GL}_2(F)$. Let $K_c$ be a subgroup of $\mathrm{GL}_2(F)$ contained in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178), that is, the subgroup of those $g$ whose image under `localEmbed` in $\mathrm{GL}_2$ of the finite adeles lies in `AdelicLevel.finiteLevelOne` for the ideal $\top$ (both the matrix and its inverse satisfying `IsLevelOneMatrix` at that ideal); assume $B(gk)=B(g)$ for all $k\in K_c$ and all $g$. Let $T$ be a finite index set, $c\colon T\to\mathbb{R}$ and $k_\bullet\colon T\to\mathrm{GL}_2(F)$ with $k_i\in K_c$ for $i\in T$. Equip $\mathrm{GL}_2(F)$ with its Borel $\sigma$-algebra. Then for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, every Haar measure $\mu_{N}$ on the range of $x\mapsto n(x)$ (the subgroup `unipotentGL2Hom.range`), and every $s\in\mathbb{C}$: if $g\mapsto A(g)B(g)\,|\det g|^{s-1/2}$ is integrable for $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of that unipotent subgroup relative to $\mu_N$, where $|\cdot|$ is `modulus` (the module of $F$, equal to the norm on the completion), then $g\mapsto\bigl(\sum_{i\in T}c_i A(g k_i)\bigr)B(g)\,|\det g|^{s-1/2}$ is also integrable for that measure, and the local Rankin–Selberg integral [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16), namely the integral of $W(g)F(g)\,|\det g|^{s-1/2}$ against the density-weighted measure, taken with $W=\sum_{i\in T}c_i A(\,\cdot\,k_i)$ and $F=B$, equals $\bigl(\sum_{i\in T}c_i\bigr)$ times its value with $W=A$, $F=B$.
--
--   This is the bookkeeping step permitting the first factor of a local Rankin–Selberg integral over $N\backslash\mathrm{GL}_2$ to be replaced by a finite real combination of right translates by elements of a level subgroup fixing the second factor, at the cost of the total mass $\sum_i c_i$; in particular it allows averaging over such a level group. It is used in the construction of the local functional equation and dual Jacquet integral comparison at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_rsLocalIntegral_finset_sum_translate_eq_sum_mul_rsLocalIntegral_of_le_localLevelOne.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal

theorem LanglandsTunnell.RankinSelberg.rsLocalIntegral_finset_sum_translate_eq_sum_mul_rsLocalIntegral_of_le_localLevelOne
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ : AddChar (p.adicCompletion ℚ) ℂ)
    (A B : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hA : Continuous A) (hB : Continuous B)
    (hAlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), A (unipotentGL2 x * g) = θ⁻¹ x * A g)
    (hBlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), B (unipotentGL2 x * g) = θ x * B g)
    (Kc : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hKc : Kc ≤ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)
    (hBK : ∀ k ∈ Kc, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), B (g * k) = B g)
    {ι : Type} (T : Finset ι) (c : ι → ℝ) (kf : ι → GL (Fin 2) (p.adicCompletion ℚ)) (hkf : ∀ i ∈ T, kf i ∈ Kc) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure] (s : ℂ),
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (A g * B g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
            (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) →
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((∑ i ∈ T, (c i : ℂ) * A (g * kf i)) * B g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
            (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) ∧
      RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) s
          (fun g => ∑ i ∈ T, (c i : ℂ) * A (g * kf i)) B =
        ((∑ i ∈ T, c i : ℝ) : ℂ) *
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) s A B := by sorry
