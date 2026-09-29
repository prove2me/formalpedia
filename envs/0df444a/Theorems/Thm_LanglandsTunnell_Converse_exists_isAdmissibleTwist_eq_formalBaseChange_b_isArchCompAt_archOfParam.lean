-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_isAdmissibleTwist_eq_formalBaseChange_b_isArchCompAt_archOfParam
-- name    : LanglandsTunnell.Converse.exists_isAdmissibleTwist_eq_formalBaseChange_b_isArchCompAt_archOfParam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/b44df753-b896-5fb0-8b77-28fcd9757dc8
-- title:
--   Admissible twist on K matching a formal base change
-- statement:
--   Let $K$ be a number field whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, and let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with values in $\mathbb{C}$, i.e. a nonzero level ideal together with families $a,b$ indexed by the height-one primes of $\mathcal{O}_{\mathbb{Q}}$. Let $R$ be a smooth cusp realization, at the pins `productionPinsGeneral ℚ`, of the rescaled eigensystem `Φ.toRawCentral` (same level and $a$, with $b$ replaced by $v\mapsto (\mathrm{cNorm}\,v)^{-1}b_v$), so $R$ carries a nonvanishing function on the adelic $GL_2$, a central character on the pinned centre, level invariance, and Hecke and central eigenvalue relations away from a finite exceptional set; assume `R.toFun` is continuous. Let $P$ be a real archimedean parameter, with central exponent $e$ and central sign $a\in\mathbb{Z}/2$, and assume that at each real infinite place $w$ of $\mathbb{Q}$ the idele class character obtained from `R.centralChar` has archimedean component $x\mapsto \|x\|^{m_w(e+1)}(\iota_w(x)/\|x\|)^{a}$, where $m_w$ is the multiplicity of $w$. Finally let $S^0_{\mathbb{Q}}$ be a finite set of primes with $\|\Phi.b\,p\|=1$ for all $p\notin S^0_{\mathbb{Q}}$. Then there exist a finite set $T_{\mathbb{Q}}$ of primes of $\mathcal{O}_{\mathbb{Q}}$ and a homomorphism $\omega$ from the idele units of $K$ to $\mathbb{C}^{\times}$ which is an idele class character, continuous and unitary, such that: for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ whose underlying prime of $\mathcal{O}_{\mathbb{Q}}$ lies outside $T_{\mathbb{Q}}$, the local character of $\omega$ at $\mathfrak{P}$ is trivial on the units of the local integers and $\omega(\varpi_{\mathfrak{P}})=(\Phi.b\,(\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}))^{f}$, the value at $\mathfrak{P}$ of the $b$-family of `formalBaseChange ℚ K Φ`, with $f$ the residue degree; at every real place $w$ of $K$ the archimedean component of $\omega$ is $x\mapsto \|x\|^{m_w e}(\iota_w(x)/\|x\|)^{a}$, the exponent and sign of $P$ transported to $w$; and at every complex place $w$ of $K$ the archimedean component is given in the same shape by the central exponent and central twist of the complex parameter `P.baseChange` attached to $P$.
--
--   This is the central-character input to the converse step of Langlands–Tunnell base change: it produces, from a realised Hecke eigensystem over $\mathbb{Q}$ with unitary central data, the admissible idele class character of $K$ whose uniformizer values are the $b$-values of the formal base change, with prescribed archimedean components, the shift $e+1\mapsto e$ recording the raw normalisation by the idelic norm. It is used in the construction of the base-changed automorphic datum over $K$ from its Whittaker coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_isAdmissibleTwist_eq_formalBaseChange_b_isArchCompAt_archOfParam.lean

import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open NumberField.TateGlobal

theorem LanglandsTunnell.Converse.exists_isAdmissibleTwist_eq_formalBaseChange_b_isArchCompAt_archOfParam
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (hR : Continuous R.toFun)
    (P : RealArchParam)
    (hP : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          (P.centralExponent + 1) (P.centralSign.val : ℤ))
    (SQ₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)))
    (hb : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), p ∉ SQ₀ → ‖Φ.b p‖ = 1) :
    ∃ Tq : Finset (HeightOneSpectrum (𝓞 ℚ)), ∃ ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      IsAdmissibleTwist K ω ∧
      (∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) ∉ Tq →
      IsUnramifiedCharAt ω 𝔓 ∧
        ((ω (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) = (formalBaseChange ℚ K Φ).b 𝔓) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchCompAt K ω w (archOfParamR K P w hw).centralExponent
        ((archOfParamR K P w hw).centralSign.val : ℤ)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchCompAt K ω w (archOfParamC K P w hw).centralExponent (archOfParamC K P w hw).centralTwist) := by sorry
