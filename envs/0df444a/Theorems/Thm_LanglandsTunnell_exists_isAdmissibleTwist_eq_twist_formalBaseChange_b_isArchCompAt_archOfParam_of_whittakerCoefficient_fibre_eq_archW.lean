-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_isAdmissibleTwist_eq_twist_formalBaseChange_b_isArchCompAt_archOfParam_of_whittakerCoefficient_fibre_eq_archW
-- name    : LanglandsTunnell.exists_isAdmissibleTwist_eq_twist_formalBaseChange_b_isArchCompAt_archOfParam_of_whittakerCoefficient_fibre_eq_archW
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/0c437df5-79c1-556d-89c4-e589e048bbc4
-- title:
--   Admissible twist matching the unitary formal base change of Φ
-- statement:
--   Let $K$ be a number field, with $\mathcal O_K$ an integral $\mathcal O_{\mathbb Q}$-algebra, let $c,u,d_1,d_2$ be real with $0<c$, $0<d_1<d_2$, and let $T$ be a finite set of elements of $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$; write $D=\bigcup_{x\in T}\{g x : g \in \mathfrak S\}$ for the union of right translates by $T$ of the centre-cut Siegel set $\mathfrak S$ of parameters $(c,u,d_1,d_2)$ (finite part integral, local height $\ge c$ and $x$-window $\le u^2$ at every infinite place, archimedean determinant norms in $[d_1,d_2]$), and assume $D$ meets every orbit $\mathrm{GL}_2(\mathbb Q)\,g\,Z(\mathbb A_{\mathbb Q})$. Let $\Phi$ be a complex Hecke eigensystem over $\mathbb Q$, let $P$ be a real archimedean parameter, $\mathrm{archC}$ a complex parameter at each complex place of $\mathbb Q$, and $dR$, $dC$ archimedean Whittaker data of type $\mathrm{ArchDatumR}\,P$ at each real place and $\mathrm{ArchDatumC}$ at each complex place (the complex data being vacuous over $\mathbb Q$). The hypothesis $\mathrm{ArchOccursInClassOf}$ asks for a Hecke eigensystem $\Theta'$ agreeing with $\Phi$ outside a finite set of primes and a continuous smooth cusp realization $R'$ for the central renormalisation $\Theta'.\mathrm{toRawCentral}$ (values $b_v$ divided by $\mathrm{cNorm}\,v$) at the production pins of $D$ (adelic Haar measure, full central subgroup, levels $\mathrm{levelOne}\,N\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}\,v$, additive measure conditioned to the adelic box), such that for $\varphi=R'.\mathrm{toFun}$ there is $g_0$ with: the Whittaker coefficient of $\varphi$ at $\alpha=1$ against the standard additive character is nonzero at some $g$ with the same finite part as $g_0$, and there is $z\in\mathbb C$ with $W_\varphi(g)=\bigl(\prod_w \mathrm{archDetNorm}_w(g)^{w.\mathrm{mult}}\bigr)^{-1/2}\,\mathrm{archW}(P,\mathrm{archC},dR,dC)(g)\,z$ for all $g$ with the finite part of $g_0$. Assume moreover that the central exponent of $P$ has real part $0$. Then there exist a finite set $T_q$ of primes of $\mathcal O_{\mathbb Q}$ and a homomorphism $\omega:(\mathbb A_K)^\times\to\mathbb C^\times$ which is an admissible twist (trivial on $K^\times$, continuous, unitary), such that for every finite place $v$ of $K$ whose restriction to $\mathcal O_{\mathbb Q}$ lies outside $T_q$, $\omega$ is unramified at $v$ and its value at the uniformizer idele of $v$ equals the $b$-value at $v$ of the twist of the formal base change $\mathrm{formalBaseChange}\,\mathbb Q\,K\,\Phi$ by $v\mapsto (\mathrm{absNorm}\,v)^{-1/2}$, that is $(\mathrm{absNorm}\,v)^{-1}\,\Phi.b(v\cap\mathcal O_{\mathbb Q})^{f(v)}$ with $f(v)$ the inertia degree; and for every real place $w$ of $K$ the archimedean component of $\omega$ at $w$ is $x\mapsto \|x\|^{w.\mathrm{mult}\cdot u_P}(\iota_w(x)/\|x\|)^{a}$ with $u_P$ the central exponent of $P$ and $a$ the integer lift of its central sign, while for every complex place $w$ of $K$ the same formula holds with the central exponent and central twist of the base change $P.\mathrm{baseChange}$ of $P$ in place of $u_P$ and $a$.
--
--   This is the central-character package attached to the unitary normalisation of the formal base change to $K$ of a rational Hecke eigensystem realised by a cuspidal Whittaker function with prescribed archimedean behaviour: an idele class character of $K$ whose unramified values reproduce the base-changed $b$-table normalised by $(N v)^{-1/2}$ and whose archimedean components are the central quasi-characters of the parameter $P$ and of its base change. It feeds the pinned-niceness statement for the twisted $L$-data of a formal base change, which is its sole consumer here.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_isAdmissibleTwist_eq_twist_formalBaseChange_b_isArchCompAt_archOfParam_of_whittakerCoefficient_fibre_eq_archW.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open NumberField.TateGlobal
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

theorem LanglandsTunnell.exists_isAdmissibleTwist_eq_twist_formalBaseChange_b_isArchCompAt_archOfParam_of_whittakerCoefficient_fibre_eq_archW
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (hWF : ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
        (fun φ => ∃ g₀ : AdelicGL2 (𝓞 ℚ) ℚ,
          (∃ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ ∧
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g ≠ 0) ∧
          ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g =
              (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                archW (fun _ _ => P) archC dR dC g * z))
    (hP0 : (RealArchParam.centralExponent P).re = 0) :
    ∃ (Tq : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
      IsAdmissibleTwist K ω ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v.under (𝓞 ℚ) ∉ Tq →
        IsUnramifiedCharAt ω v ∧
          ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) = ((formalBaseChange ℚ K Φ).twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal),
        IsArchCompAt K ω w (archOfParamR K P w hw).centralExponent ((archOfParamR K P w hw).centralSign.val : ℤ)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex),
        IsArchCompAt K ω w (archOfParamC K P w hw).centralExponent (archOfParamC K P w hw).centralTwist) := by sorry
