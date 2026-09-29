-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne
-- name    : LanglandsTunnell.RankinSelberg.exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/93a18421-3d15-50bd-8011-64bb9b991225
-- title:
--   Kirillov bump in a twisted Whittaker translate span
-- statement:
--   Fix a finite place $p$ of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$) and characters $\chi,\xi,\theta_0 : (\mathbb{Q}_p)^\times \to \mathbb{C}^\times$, where $\mathbb{Q}_p$ denotes the completion at $p$. Assume $\chi$ has conductor exponent $k_p$ and $\xi$ has conductor exponent $B$ with $B < k_p$, in the sense that each is trivial on the units $u$ with $v(u)=1$ and $v(u-1)\le\exp(-c)$ (all units of valuation $1$ when $c=0$), and non-trivial on the corresponding set for every smaller exponent. Let $N$ be a non-zero ideal of $\mathcal{O}_{\mathbb{Q}}$ and let $w_2 : \mathrm{GL}_2(\mathbb{Q}_p)\to\mathbb{C}$ be non-zero, satisfy $w_2(\begin{pmatrix}1&x\\0&1\end{pmatrix}g)=\psi_p(x)\,w_2(g)$ for the standard local additive character $\psi_p$, be right invariant under the subgroup of $\mathrm{GL}_2(\mathbb{Q}_p)$ obtained by pulling back the adelic level-one group of $N$ along the embedding at $p$, and satisfy $w_2(\mathrm{diag}(z,z)g)=\theta_0(z)w_2(g)$. Then there is $w'$ in the $\mathbb{C}$-span of the right translates $g\mapsto w_2(gh)$, $h\in\mathrm{GL}_2(\mathbb{Q}_p)$, such that the twisted function $w'^\sharp(g)=\chi(\det g)\xi(\det g)^{-1}w'(g)$ satisfies: for some $c_0\neq 0$, $w'^\sharp(\mathrm{diag}(y,1))=c_0$ when $v(y)=\exp(2k_p)$ and $0$ otherwise; $w'^\sharp$ is again $\psi_p$-equivariant for upper unipotents; it has central character $\theta_0\cdot(\chi\xi^{-1})^2$; and it is invariant under right translation by some open subgroup. (With the normalisation in which a uniformiser has valuation $\exp(-1)$, the shell condition is $\mathrm{ord}_p(y)=-2k_p$.)
--
--   This is the local $\mathrm{GL}_2$ input of Jacquet–Langlands Proposition 2.9, in the form used for highly ramified twists: inside the span of right translates of a Whittaker function of level dividing $N$ one finds a vector whose twist by $\chi\xi^{-1}\circ\det$ has Kirillov function supported on a single valuation shell determined by the conductor of $\chi$. It feeds the construction of a Schwartz–Bruhat test vector with non-vanishing local Rankin–Selberg pairing for deeply ramified twists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne.lean

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
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

theorem LanglandsTunnell.RankinSelberg.exists_mem_span_twist_det_kirillov_eq_indicator_shell_of_localLevelOne
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (kp : ℕ) (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ kp)
    (ξ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (B : ℕ) (hξB : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p ξ B) (hBk : B < kp)
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g) :
    ∃ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      (∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ y : (p.adicCompletion ℚ)ˣ,
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (diagUnitGL2 y) =
          if Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (((2 * kp : ℕ)) : ℤ) then c₀ else 0) ∧

      (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (unipotent x * g) =
          NumberField.StandardAddChar.psiLocal ℚ p x *
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g) ∧
      (∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) =
          (((θ₀ * (χ * ξ⁻¹) ^ 2) z : ℂˣ) : ℂ) *
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g) ∧
      (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) (g * k) =
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w' g) g) := by sorry
