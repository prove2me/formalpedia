-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_godementZeta2_comp_transposeInvN_eq_godementZeta2_conj_of_central
-- name    : LanglandsTunnell.RankinSelberg.godementZeta2_comp_transposeInvN_eq_godementZeta2_conj_of_central
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/a0305786-d525-5d95-8246-00ac694f55c0
-- title:
--   Transpose-inverse symmetry of the local GL₂ Godement zeta integral
-- statement:
--   Fix a finite place $p$ of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, and write $F = \mathbb{Q}_p$ for the corresponding completion. Let $\theta_0 : F^\times \to \mathbb{C}^\times$ be a homomorphism, and let $w : GL_2(F) \to \mathbb{C}$ satisfy $w(\mathrm{scalar}(z)\,g) = \theta_0(z)\,w(g)$ for all $z \in F^\times$ and all $g$, where $\mathrm{scalar}(z)$ is the central matrix $z \cdot I_2$. Let $w_J \in GL_2(F)$ be an element whose underlying matrix is $\begin{pmatrix} 0 & 1 \\ -1 & 0\end{pmatrix}$. Then, with $GL_2(F)$ carrying the Borel $\sigma$-algebra of its topology, for every Haar measure $\mu_2$ on $GL_2(F)$, every function $\Phi' : M_2(F) \to \mathbb{C}$, every homomorphism $\chi' : F^\times \to \mathbb{C}^\times$ and every $s \in \mathbb{C}$,
--   $$\int_{GL_2(F)} w({}^t g^{-1})\,\Phi'(g)\,\chi'(\det g)\,\lVert \det g\rVert^{s}\,d\mu_2(g) = \int_{GL_2(F)} w(g)\,\Phi'(w_J^{-1} g\, w_J)\,\theta_0(\det g)^{-1}\chi'(\det g)\,\lVert \det g\rVert^{s}\,d\mu_2(g),$$
--   where ${}^t g^{-1}$ denotes `transposeInvN`, the transpose of the inverse matrix of $g$, and $\lVert \cdot \rVert$ is the modulus given by the distributive Haar character of $F$ (with value $0$ at $0$). Both sides are Bochner integrals, so the identity includes the case where neither integrand is integrable.
--
--   This is the local input to the functional equation of the Godement–Jacquet zeta integral on $GL_2$: it realises the substitution $g \mapsto {}^t g^{-1}$ on the matrix coefficient as a twist of the Schwartz–Bruhat datum by conjugation together with the twist of the quasi-character by the inverse central character, the local shadow of the identification of the contragredient representation with $\omega^{-1}\otimes\pi$. It is used in the analysis of the Godement zeta integrals attached to Whittaker functions, namely in the derivation of their Laurent expansions and of their rationality from the functional equations of the torus zeta integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_godementZeta2_comp_transposeInvN_eq_godementZeta2_conj_of_central.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
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

theorem LanglandsTunnell.RankinSelberg.godementZeta2_comp_transposeInvN_eq_godementZeta2_conj_of_central
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0]) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (Φ' : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (χ' : (p.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ),
      godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (transposeInvN (Fin 2) g)) Φ' χ' s =
        godementZeta2 p μ₂ w
          (fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
            Φ' (((wJ⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X * (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))))
          (θ₀⁻¹ * χ') s := by sorry
