-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_aestronglyMeasurable_godementUnfold_integrand
-- name    : LanglandsTunnell.RankinSelberg.aestronglyMeasurable_godementUnfold_integrand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/ce77d918-ed8b-5499-971b-c173c2168184
-- title:
--   Measurability of the unfolded Godement double integrand
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, with completion $\mathbb{Q}_p$. Fix a pair $\mu = (\mu_0,\mu_1)$ of locally constant homomorphisms $\mathbb{Q}_p^\times \to \mathbb{C}^\times$ and reals $\sigma_0,\sigma_1$ with $\|\mu_i(a)\| = \|a\|^{\sigma_i}$ for all $a$, and assume $\sigma_1 < \sigma_0$. Let $\varphi : \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ lie in `principalSeries2`, i.e. $\varphi$ is locally constant, satisfies $\varphi(u(x)g) = \varphi(g)$ for upper unipotent $u(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, and $\varphi(\mathrm{diag}(a)g) = \mathrm{torusChar2}(\mu)(a)\,\mathrm{halfModulus2}(a)\varphi(g)$. Let $\chi : \mathbb{Q}_p^\times \to \mathbb{C}^\times$, $\varphi_1$ on $2\times2$ matrices and $\varphi_2$ on $\mathbb{Q}_p \times \mathbb{Q}_p$ be locally constant, and let $w : \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ be invariant under right translation by some open subgroup. With Borel measurable structures on $\mathbb{Q}_p$ and on $\mathrm{GL}_2(\mathbb{Q}_p)$, the assertion is: for every measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_p)$, every measure $\mu_{N_2}$ on the range of `unipotentGL2Hom`, every measure $\nu$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ and every $s \in \mathbb{C}$, the function $$(g,h) \mapsto \varphi_1(h)\chi(\det h)|\det h|^{s+1/2} \cdot \Big(\int_{\mathbb{Q}_p} \psi_p(x)\,\varphi\big(\begin{pmatrix}0&1\\1&0\end{pmatrix}u(x)g\big)\,dx\Big)\, w(gh)\, \varphi_2(g_{10},g_{11})\,|\det g|^{s}$$ is a.e. strongly measurable for the product of $\mu_2$ weighted by the quotient density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of the unipotent range with respect to $\mu_{N_2}$ and of $\nu$. Here $|\cdot|$ is `modulus`, the inner integral is against the self-dual Haar measure `selfDualHaarAt` and $\psi_p$ is the standard local additive character `psiLocal`.
--
--   This is the measurability input for the local Rankin–Selberg integral at $p$ after Godement unfolding: the double integrand, assembled from a principal-series vector through its Jacquet integral, a locally constant Schwartz-type datum and a right-$U$-invariant function $w$, is a.e. strongly measurable for any choice of the three measures involved, so that Fubini and integrability estimates may be applied to it. It is used by [`LanglandsTunnell.RankinSelberg.exists_forall_integrable_godementUnfold_of_principalSeries2_of_admissible_ed2`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_integrable_godementUnfold_of_principalSeries2_of_admissible_ed2), where the corresponding integrability is established.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_aestronglyMeasurable_godementUnfold_integrand.lean

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

theorem LanglandsTunnell.RankinSelberg.aestronglyMeasurable_godementUnfold_integrand
    (p : HeightOneSpectrum (𝓞 ℚ))

    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hμ : ∀ i, IsLocallyConstant (μ i))
    (σ : Fin 2 → ℝ)
    (hσ : ∀ (i : Fin 2) (a : (p.adicCompletion ℚ)ˣ), ‖((μ i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0)
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ₁ : IsLocallyConstant φ₁)
    (φ₂ : (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ) (hφ₂ : IsLocallyConstant φ₂)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) (μN₂ : Measure ↥(unipotentGL2Hom (R := (p.adicCompletion ℚ))).range) (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) (s : ℂ),
      AEStronglyMeasurable (fun gh : GL (Fin 2) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
          (φ₁ (gh.2 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det gh.2) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det gh.2 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 1 / 2)) *
            ((∫ x : (p.adicCompletion ℚ), NumberField.StandardAddChar.psiLocal ℚ p x *
                φ (antidiagonal2 p * upperUnipotent2 p x * gh.1) ∂(selfDualHaarAt ℚ p)) *
              w (gh.1 * gh.2) *
              φ₂ ((gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0, (gh.1 : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1) *
              ((modulus ((Matrix.GeneralLinearGroup.det gh.1 : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ s))
        ((μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := (p.adicCompletion ℚ))).range μN₂)).prod ν) := by sorry
