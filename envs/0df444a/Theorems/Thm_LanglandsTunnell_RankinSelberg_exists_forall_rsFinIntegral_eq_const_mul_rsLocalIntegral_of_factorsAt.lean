-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_rsFinIntegral_eq_const_mul_rsLocalIntegral_of_factorsAt
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_rsFinIntegral_eq_const_mul_rsLocalIntegral_of_factorsAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/fc6b9dcb-8c72-5fe9-a2e2-b3a8161909ff
-- title:
--   One-place factorisation of the finite Rankin–Selberg integral
-- statement:
--   Fix a height-one prime $p$ of $\mathcal O_{\mathbb Q}$, a Haar measure $\mu$ on the finite-adelic group `finiteAdelicGL2Subgroup ℚ` (the kernel of the archimedean projection on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$), a Haar measure $\mu_N$ on [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43), the adelic upper unipotent subgroup viewed inside that finite-adelic group, two functions $W',F' : \mathrm{GL}_2(\mathbb A_{\mathbb Q}) \to \mathbb C$ each invariant under right multiplication by the image of $\mathrm{GL}_2(\mathbb Q_p)$ under `placeEmbed ℚ p`, such that the product $W'F'$ is invariant under left multiplication by [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43), and $s \in \mathbb C$; $\mathrm{GL}_2(\mathbb Q_p)$ carries its Borel structure. The assertion is that for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb Q_p)$ and every Haar measure $\mu_{N,2}$ on the range of `unipotentGL2Hom`, i.e. on the group of matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, $x \in \mathbb Q_p$, there exists a single constant $C \in \mathbb C$, independent of the local data, with the following property: whenever $W,F$ on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$ and $w,f$ on $\mathrm{GL}_2(\mathbb Q_p)$ satisfy $W(g) = w(\mathrm{loc}_p g)\,W'(g)$ and $F(g) = f(\mathrm{loc}_p g)\,F'(g)$ for all $g$, where $\mathrm{loc}_p$ is the component homomorphism `localAt ℚ p`, the product $wf$ is invariant under left multiplication by `unipotent x` for all $x \in \mathbb Q_p$, and $g \mapsto W(g)F(g)$ is measurable on the finite-adelic group, then $$\mathrm{rsFinIntegral}(\mu,\mu_N,s;W,F) = C \cdot \mathrm{rsLocalIntegral}(\mu_2,N,\mu_{N,2},\delta_p,s;w,f).$$ Here both sides are integrals of $W F$, respectively $wf$, against $\lVert\det\rVert^{s-1/2}$ — the idele norm of the determinant globally, the local modulus $\delta_p(g) = \lvert\det g\rvert_p$ locally — taken against the given Haar measure reweighted by the [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the relevant unipotent subgroup, so that each side is a Rankin–Selberg integral over the quotient by that unipotent group.
--
--   This is the splitting-off of the Euler factor at $p$ from the finite-adelic Rankin–Selberg zeta integral, in proportionality form: with the prime-to-$p$ data $W',F'$ frozen, the global finite integral is a fixed multiple of the local integral at $p$, with the multiple uniform in the local pair $(w,f)$. It feeds the assembly of global Rankin–Selberg integrals out of their local factors in the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_rsFinIntegral_eq_const_mul_rsLocalIntegral_of_factorsAt.lean

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
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem LanglandsTunnell.RankinSelberg.exists_forall_rsFinIntegral_eq_const_mul_rsLocalIntegral_of_factorsAt
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]

    (W' F' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hW' : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), W' (g * placeEmbed ℚ p x) = W' g)
    (hF' : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), F' (g * placeEmbed ℚ p x) = F' g)
    (hN' : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      W' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W' (g : AdelicGL2 (𝓞 ℚ) ℚ) * F' (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (s : ℂ) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
    ∃ C : ℂ, ∀ (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (w f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),

      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W g = w (localAt ℚ p g) * W' g) →
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, F g = f (localAt ℚ p g) * F' g) →

      (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        w (unipotent x * g) * f (unipotent x * g) = w g * f g) →

      Measurable (fun g : finiteAdelicGL2Subgroup ℚ => W g * F g) →
      RSCarrier.rsFinIntegral μ μN s (fun g => W g) (fun g => F g) =
        C * RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s w f := by sorry
