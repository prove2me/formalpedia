-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_godementZeta2_eq_mul_rsLocalIntegral_rowSlice
-- name    : LanglandsTunnell.RankinSelberg.exists_pos_forall_godementZeta2_eq_mul_rsLocalIntegral_rowSlice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/21a1a3e5-c582-56be-9e19-e6bdd857b965
-- title:
--   Local Godement zeta integral as a Rankin–Selberg row-slice integral
-- statement:
--   Fix a prime $p$ of $\mathcal O_{\mathbb Q}$, write $F = \mathbb Q_p$ for the completion, and equip $F$ and $\mathrm{GL}_2(F)$ with their Borel $\sigma$-algebras. The assertion is: for every Haar measure $\mu_2$ on $\mathrm{GL}_2(F)$ and every Haar measure $\mu_{N_2}$ on the image $N_2$ of the homomorphism $x \mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$ from $(F,+)$ into $\mathrm{GL}_2(F)$, there exists $\kappa > 0$, depending only on these two measures, such that the following holds for all data: a locally constant $w : \mathrm{GL}_2(F) \to \mathbb C$ with $w(n(x)g) = \psi_p(x)\,w(g)$ for all $x \in F$, $g \in \mathrm{GL}_2(F)$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_p$ is the local component at $p$ of the standard additive character of the adeles of $\mathbb Q$; a locally constant, compactly supported $\Phi : M_2(F) \to \mathbb C$; a locally constant homomorphism $\chi : F^\times \to \mathbb C^\times$; and $s \in \mathbb C$ such that $g \mapsto w(g)\,\Phi(g)\,\chi(\det g)\,\lVert\det g\rVert^s$ is $\mu_2$-integrable, $\lVert\cdot\rVert$ denoting the module (the distributive Haar character of multiplication, extended by $0$ at $0$). Then the Godement zeta integral $\int_{\mathrm{GL}_2(F)} w(g)\,\Phi(g)\,\chi(\det g)\,\lVert\det g\rVert^{s}\,d\mu_2(g)$ equals $\kappa$ times $\int_{\mathrm{GL}_2(F)} A(g)\,w(g)\,\lVert \det g\rVert^{(s+1/2)-1/2}$ taken against $\mu_2$ weighted by the density attached to $N_2$ and $\mu_{N_2}$, where the first slot is the row slice $A(g) = \bigl(\int_F \psi_p(x)\,\Phi(n(x)g)\,dx\bigr)\chi(\det g)$, the inner integral being against the self-dual Haar measure on $F$ (the additive Haar measure of $\mathcal O_{F}$ rescaled by $(\mathrm{N}p)^{-\mathrm{level}(\psi_p)/2}$), and the second slot is $w$ itself.
--
--   This is the first unfolding step that rewrites a local Godement–Jacquet zeta integral on $\mathrm{GL}_2(\mathbb Q_p)$ as a Rankin–Selberg integral over $N_2 \backslash \mathrm{GL}_2(\mathbb Q_p)$, realised in the formalisation as an integral against $\mu_2$ weighted by a quotient density, with the Whittaker function $w$ in one slot and the $\psi_p$-row slice of $\Phi$ twisted by $\chi \circ \det$ in the other, and with the spectral parameter shifted by $1/2$. It is used in the analysis of the Laurent behaviour and rationality of the shifted Godement zeta integrals attached to Whittaker data in the converse-theorem part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_godementZeta2_eq_mul_rsLocalIntegral_rowSlice.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_pos_forall_godementZeta2_eq_mul_rsLocalIntegral_rowSlice
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∃ κ : ℝ, 0 < κ ∧
        ∀ (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant w →
          (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g) →
        ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
        ∀ (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ), IsLocallyConstant χ →
        ∀ s : ℂ,
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s) μ₂ →
          godementZeta2 p μ₂ w Φ χ s =
            (κ : ℂ) * RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              (s + 1 / 2)

              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p)) *
                ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ))

              w := by sorry
