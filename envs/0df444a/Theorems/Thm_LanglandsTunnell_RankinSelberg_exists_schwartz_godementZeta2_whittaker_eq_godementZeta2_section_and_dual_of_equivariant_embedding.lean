-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_schwartz_godementZeta2_whittaker_eq_godementZeta2_section_and_dual_of_equivariant_embedding
-- name    : LanglandsTunnell.RankinSelberg.exists_schwartz_godementZeta2_whittaker_eq_godementZeta2_section_and_dual_of_equivariant_embedding
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/1ed8b711-38f4-5bc4-ab2f-61713df290e0
-- title:
--   Whittaker Godement zeta equals that of its principal-series image
-- statement:
--   Fix a finite place $p$ of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), write $F=\mathbb{Q}_p$ for the completion, and let $N\neq 0$ be an ideal of $\mathcal{O}_{\mathbb{Q}}$. Let $w_{2\mathrm{base}}:\mathrm{GL}_2(F)\to\mathbb{C}$ satisfy: $w_{2\mathrm{base}}\bigl(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\bigr)g)=\psi_p(x)\,w_{2\mathrm{base}}(g)$ for the standard local additive character $\psi_p$; right invariance under the subgroup [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) of $\mathrm{GL}_2(F)$, namely the preimage of the finite-adelic level-one group of $N$ under the local embedding; $w_{2\mathrm{base}}\neq 0$; an irreducibility condition, that every nonzero $w$ in the $\mathbb{C}$-span $V$ of the right translates $g\mapsto w_{2\mathrm{base}}(gh)$ has $w_{2\mathrm{base}}$ in the span of its own right translates; and an admissibility condition, that for every open subgroup $U$ there is a finite set $B$ of functions whose span contains every $U$-right-invariant element of $V$. Let $\lambda=(\lambda_0,\lambda_1)$ be characters of $F^\times$ and let $\Phi_e$ be a $\mathbb{C}$-linear endomorphism of the functions on $\mathrm{GL}_2(F)$ which on $V$ commutes with right translation, is injective, and takes values in `principalSeries2` of $\lambda$, i.e. the locally constant functions $f$ with $f(u(x)g)=f(g)$ and $f(\mathrm{diag}(a)g)=\mathrm{torusChar2}(a)\,\mathrm{halfModulus2}(a)f(g)$. Let $\chi:F^\times\to\mathbb{C}^\times$ be a locally constant character. Then, with the Borel structures on $F$ and $\mathrm{GL}_2(F)$, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$, every $w\in V$ and every locally constant compactly supported $\Phi$ on $M_2(F)$, there exist a locally constant compactly supported $\Phi_t$ on $M_2(F)$ and a finite set $S\subset\mathrm{GL}_2(F)$ such that for every $s\in\mathbb{C}$: (i) if $g\mapsto w(g)\Phi(g)\chi(\det g)|\det g|^s$ is $\mu_2$-integrable and, for each $t\in S$, $g\mapsto \Phi_e w(g)\,\Phi(t^{-1}g)\,\chi(\det g)|\det g|^s$ is $\mu_2$-integrable, then the zeta integrals satisfy $Z(w,\Phi,\chi,s)=Z(\Phi_e w,\Phi_t,\chi,s)$, where $Z(c,\varphi,\chi,s)=\int_{\mathrm{GL}_2(F)}c(g)\varphi(g)\chi(\det g)|\det g|^s\,d\mu_2$ and $|\cdot|$ is the modulus; and (ii) the corresponding identity $Z(w\circ\iota,\widehat{\Phi},\chi^{-1},s)=Z(\Phi_e w\circ\iota,\widehat{\Phi_t},\chi^{-1},s)$, where $\iota(g)=(g^{-1})^{\mathsf T}$ and $\widehat{\;}$ is the two-variable column-wise Fourier transform `matFourier22` with respect to $\psi_p$, under the analogous integrability hypotheses for $w\circ\iota$ against $\widehat{\Phi}$ and for $\Phi_e w\circ\iota$ against the transforms of $X\mapsto\Phi(t^{-1}X)$, $t\in S$.
--
--   This is the local step, in the style of Godement's method, by which the Godement–Jacquet zeta integral of a Whittaker vector and of its Fourier dual are replaced by those of the corresponding section of a principal series, at the cost of replacing the test function and allowing a finite set of auxiliary translates. It feeds the derivation of the cleared functional equation for Whittaker Godement zeta integrals from the functional equation for torus zeta integrals of Borel eigenfunctionals, cited by [`LanglandsTunnell.RankinSelberg.forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_borelEigenfunctional`](thm.html#LanglandsTunnell.RankinSelberg.forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_borelEigenfunctional).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_schwartz_godementZeta2_whittaker_eq_godementZeta2_section_and_dual_of_equivariant_embedding.lean

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
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2

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

theorem LanglandsTunnell.RankinSelberg.exists_schwartz_godementZeta2_whittaker_eq_godementZeta2_section_and_dual_of_equivariant_embedding
    (p : HeightOneSpectrum (𝓞 ℚ))

    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))

    (lam : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φe : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hΦeq : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      Φe (fun g => w (g * h)) = fun g => Φe w (g * h))
    (hΦinj : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φe w = 0 → w = 0)
    (hΦPS : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), Φe w ∈ principalSeries2 p lam)

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
          ∃ Φt : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ, IsLocallyConstant Φt ∧ HasCompactSupport Φt ∧
            ∃ S : Finset (GL (Fin 2) (p.adicCompletion ℚ)), ∀ s : ℂ,
              ((Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s) μ₂ →
                (∀ t ∈ S, Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    Φe w g * Φ (((t⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
                      ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s) μ₂) →
                godementZeta2 p μ₂ w Φ χ s = godementZeta2 p μ₂ (Φe w) Φt χ s) ∧
              (Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    w (transposeInvN (Fin 2) g) *
                      matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                      ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s) μ₂ →
                (∀ t ∈ S, Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                    Φe w (transposeInvN (Fin 2) g) *
                      matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p)
                        (fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) => Φ (((t⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X)) (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                      ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s) μ₂) →
                godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (transposeInvN (Fin 2) g))
                    (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ s =
                  godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => Φe w (transposeInvN (Fin 2) g))
                    (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φt) χ⁻¹ s)) := by sorry
