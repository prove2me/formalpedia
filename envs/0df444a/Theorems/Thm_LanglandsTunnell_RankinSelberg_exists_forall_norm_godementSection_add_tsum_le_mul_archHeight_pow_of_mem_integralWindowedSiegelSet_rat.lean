-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_norm_godementSection_add_tsum_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_norm_godementSection_add_tsum_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/b3f333cf-a089-59d6-b929-187c66d6ec58
-- title:
--   Bruhat-series majorant for Godement sections on rational Siegel sets
-- statement:
--   Fix a Haar measure $\nu_0$ on the idele group $(\mathbb{A}_{\mathbb{Q}})^{\times}$ of $\mathbb{Q}$ (the adele ring, $\mathrm{GL}_2$ of it, and the ideles carrying their Borel $\sigma$-algebras), a function $\Phi \colon \mathbb{A}_{\mathbb{Q}}^{2} \to \mathbb{C}$ lying in the span `schwartzBruhat2` of pure tensors of Schwartz–Bruhat functions, reals $c, u$ with $c > 0$, an element $t \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, reals $e_1, e_2$ with $e_1 > 0$, and $s \in \mathbb{C}$ with $\operatorname{Re} s > 1$. Write $f$ for the Godement section `godementSection` attached to $\Phi$ at parameter $s - 1/2$ with both characters trivial and with $\alpha$ the module character `moduleChar` of $\mathbb{A}_{\mathbb{Q}}$ (the positive-real Haar modulus), i.e. $f(g)$ is the value of $\alpha(\det g)^{s}$ times the global Tate zeta integral, against $\nu_0$ and the trivial character at exponent $2s$, of $t' \mapsto \Phi(\text{bottomRowVec}(g)\,t')$. The assertion is the existence of $A \ge 0$ and $N \in \mathbb{N}$ such that for every $h$ in the integrally windowed Siegel set `integralWindowedSiegelSet` $\mathbb{Q}\,c\,u$ — that is, with finite part in `finiteIntegralGL2`, with $c \le \mathrm{archHeight}$ of its archimedean part, and with $\mathrm{xWindowSq} \le u^{2}$ at every infinite place — satisfying $\mathrm{ideleNorm}(\det(ht)) \in [e_1, e_2]$, the family $\xi \mapsto \lVert f(w\,n(\xi)\,ht) \rVert$ indexed by $\xi \in \mathbb{Q}$ is summable and $$\lVert f(ht)\rVert + \sum_{\xi \in \mathbb{Q}} \lVert f(w\,n(\xi)\,ht)\rVert \le A\,(1 + \mathrm{archHeight}_{\mathbb{Q}}(h_{\infty}))^{N},$$ where $w$ is the adelic Weyl element `adelicWeyl`, $n(\xi) = \begin{pmatrix} 1 & \xi \\ 0 & 1\end{pmatrix}$ for the image of $\xi$ in $\mathbb{A}_{\mathbb{Q}}$, $h_\infty$ the archimedean component of $h$, and $\mathrm{archHeight}_{\mathbb{Q}}$ the product over infinite places of local heights raised to their multiplicities.
--
--   This is the Eisenstein-type majorant for the two Bruhat cell contributions of a Godement section on a Siegel set intersected with a slab on the norm of the determinant: both the value at $ht$ and the full series over the unipotent translates of the Weyl cell are bounded by a fixed power of the archimedean height. It supplies the growth estimate used by [`LanglandsTunnell.RankinSelberg.exists_forall_integrableOn_norm_mul_godementSection_majorant_rat`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_integrableOn_norm_mul_godementSection_majorant_rat), the folded-integrability clause in the Rankin–Selberg integral over $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_norm_godementSection_add_tsum_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_NumberField_IdeleProductMeasure
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open NumberField.AdelicFourier
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

theorem LanglandsTunnell.RankinSelberg.exists_forall_norm_godementSection_add_tsum_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat
    (ν₀ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) [ν₀.IsHaarMeasure]
    (Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (_hΦ : Φ ∈ schwartzBruhat2 ℚ)
    (c u : ℝ) (_hc : 0 < c) (t : AdelicGL2 (𝓞 ℚ) ℚ) (e₁ e₂ : ℝ) (_he₁ : 0 < e₁)
    (s : ℂ) (_hs : 1 < s.re) :
    ∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧
      ∀ h ∈ integralWindowedSiegelSet ℚ c u,
        TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (h * t)) ∈ Set.Icc e₁ e₂ →
          (Summable fun ξ : ℚ =>
            ‖godementSection ℚ ν₀ 1 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2)
              (adelicWeyl (𝓞 ℚ) ℚ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ξ) * (h * t))‖) ∧
          ‖godementSection ℚ ν₀ 1 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2) (h * t)‖ +
              ∑' ξ : ℚ, ‖godementSection ℚ ν₀ 1 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ (s - 1 / 2)
                (adelicWeyl (𝓞 ℚ) ℚ * unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ξ) * (h * t))‖ ≤
            A * (1 + archHeight ℚ (glArch (𝓞 ℚ) ℚ h)) ^ N := by sorry
