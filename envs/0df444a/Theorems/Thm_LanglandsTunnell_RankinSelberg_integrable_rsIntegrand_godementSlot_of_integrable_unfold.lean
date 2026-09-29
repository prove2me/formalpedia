-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_integrable_rsIntegrand_godementSlot_of_integrable_unfold
-- name    : LanglandsTunnell.RankinSelberg.integrable_rsIntegrand_godementSlot_of_integrable_unfold
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/0e65cc00-e54d-5afe-9c9a-39225e33a004
-- title:
--   Integrability of the local Rankin–Selberg integrand from its unfolding
-- statement:
--   Fix a height-one prime $p$ of $\mathcal O_{\mathbb Q}$ and write $F$ for the completion $\mathbb Q_p$ and $\psi$ for the standard local additive character [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) of $F$ (the restriction to the $p$-component of the standard adelic character). Let $\chi\colon F^\times\to\mathbb C^\times$ be a monoid homomorphism, $\varphi_1\colon M_2(F)\to\mathbb C$, $\varphi_2\colon F\times F\to\mathbb C$, and $W_1,w\colon \mathrm{GL}_2(F)\to\mathbb C$, all locally constant, with $W_1(n(x)g)=\psi(-x)W_1(g)$ and $w(n(x)g)=\psi(x)w(g)$ for all $x\in F$ and $g\in\mathrm{GL}_2(F)$, where $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Equip $\mathrm{GL}_2(F)$ and $F$ with their Borel structures. The assertion is: for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, every Haar measure $\mu_{N_2}$ on the range $N$ of `unipotentGL2Hom` (the subgroup of the matrices $n(x)$), every Haar measure $\nu$ on $\mathrm{GL}_2(F)$, and every $s\in\mathbb C$, if the function $$(g,h)\mapsto \bigl(\varphi_1(h)\chi(\det h)|\det h|^{s+1/2}\bigr)\bigl(W_1(g)\,w(gh)\,\varphi_2(g_{10},g_{11})\,|\det g|^{s}\bigr)$$ is integrable for the product of $\nu$ with $\mu_2$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) attached to $N$ and $\mu_{N_2}$ (the quotient density built from the exhaustion weight, normalised along $N$-cosets, which realises integration over $N\backslash\mathrm{GL}_2(F)$), then $$g\mapsto \chi(\det g)\,|\det g|\Bigl(\int_{\mathrm{GL}_2(F)}\varphi_1(hg)\,\varphi_2\bigl((h^{-1})_{10},(h^{-1})_{11}\bigr)W_1(h^{-1})\chi(\det h)|\det h|^{1/2}\,d\nu(h)\Bigr)w(g)\,|\det g|^{s-1/2}$$ is integrable for that same weighted measure on $\mathrm{GL}_2(F)$. Here $|\cdot|$ denotes `modulus`, the module of the multiplication action on $F$.
--
--   This is the convergence half of the local unfolding step in the Rankin–Selberg theory of $\mathrm{GL}_3\times\mathrm{GL}_2$ at a finite place: absolute convergence of the Rankin–Selberg integrand attached to a Godement-type section is deduced from absolute convergence of the unfolded double integral. It feeds the computation of the local integrals and their duals in the cubic-induction step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_integrable_rsIntegrand_godementSlot_of_integrable_unfold.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.integrable_rsIntegrand_godementSlot_of_integrable_unfold
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ₁ : IsLocallyConstant φ₁)
    (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (hφ₂ : IsLocallyConstant φ₂)
    (W₁ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hW₁ : IsLocallyConstant W₁)
    (hW₁law : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W₁ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p (-x) * W₁ g)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hw : IsLocallyConstant w)
    (hwlaw : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) [μN₂.IsHaarMeasure]
      (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [ν.IsHaarMeasure]
      (s : ℂ),

      Integrable (fun gh : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
          (φ₁ (gh.2 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det gh.2) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det gh.2 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) *
            (W₁ gh.1 * w (gh.1 * gh.2) *
              φ₂ ((gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
              ((modulus ((Matrix.GeneralLinearGroup.det gh.1 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s))
        ((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)).prod ν) →
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) *
              ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
                φ₁ ((h * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  φ₂ (((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, ((h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
                  W₁ h⁻¹ * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂ν) g * w g *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)) := by sorry
