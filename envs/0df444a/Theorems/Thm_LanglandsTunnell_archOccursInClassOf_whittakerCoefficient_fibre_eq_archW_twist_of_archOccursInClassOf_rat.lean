-- Prove2me | Theorems.Thm_LanglandsTunnell_archOccursInClassOf_whittakerCoefficient_fibre_eq_archW_twist_of_archOccursInClassOf_rat
-- name    : LanglandsTunnell.archOccursInClassOf_whittakerCoefficient_fibre_eq_archW_twist_of_archOccursInClassOf_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/e1e32a57-3d50-5910-83d6-cf332d9f1a2e
-- title:
--   Fibre Whittaker factorisation transports along a norm twist
-- statement:
--   Fix real numbers $c,u,d_1,d_2$ with $0<d_1$, a finite set $T$ of elements of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and let $D=\bigcup_{x\in T}\{g x : g\in \mathrm{centreCutSiegelSet}\,\mathbb{Q}\,c\,u\,d_1\,d_2\}$, the corresponding finite union of right translates of the centre-cut Siegel set. Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex eigenvalues $a_v,b_v$ and nonzero level, let $P$ be a real archimedean parameter, let $archC$ assign a complex archimedean parameter to each complex place, and let $dR$, $dC$ assign archimedean Whittaker data $\mathrm{ArchDatumR}(P)$, resp. $\mathrm{ArchDatumC}(archC\,w)$, to the real, resp. complex, places of $\mathbb{Q}$. Let $t\in\mathbb{R}$ and let $dR'$ assign to each real place a datum for the twisted parameter $P.\mathrm{twist}\,t\,0$ whose Whittaker function satisfies $(dR')_w.W(g)=|\det g|^{t}\,(dR)_w.W(g)$ for all real $2\times 2$ matrices $g$. Write $\mathcal{W}(\varphi,g)$ for the Whittaker coefficient of $\varphi$ at $\alpha=1$ against the standard additive character, computed with the production pins attached to $D$, the level groups $N\mapsto \mathrm{levelOne}\,N\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators $\mathrm{heckeGen}\,v$ and the adelic box. Assume $\mathrm{ArchOccursInClassOf}$ holds for $D$, $\Phi$ and the following property: there exist an eigensystem $\Phi'$ agreeing with $\Phi$ outside a finite set of primes and a continuous smooth cuspidal realization $\varphi$ at those pins for $\Phi'.\mathrm{toRawCentral}$, together with $g_0$ such that $\mathcal{W}(\varphi,g)\neq 0$ for some $g$ with $\mathrm{glFin}\,g=\mathrm{glFin}\,g_0$, and a constant $z\in\mathbb{C}$ with $\mathcal{W}(\varphi,g)=\bigl(\prod_w \mathrm{archDetNorm}_w(g)^{\,\mathrm{mult}\,w}\bigr)^{-1/2}\,\mathrm{archW}(P,archC,dR,dC)(g)\,z$ for every $g$ with $\mathrm{glFin}\,g=\mathrm{glFin}\,g_0$. Then the same statement holds for the twisted eigensystem $\Phi.\mathrm{twist}\bigl(v\mapsto \mathrm{absNorm}(v)^{-t}\bigr)$, with the archimedean Whittaker function built from the constant parameter $P.\mathrm{twist}\,t\,0$, the data $dR'$ at the real places, and $archC$, $dC$ unchanged.
--
--   This is the normalisation step that lets one move a Whittaker-factorised occurrence statement along a twist by a power of the idele norm, the archimedean datum being adjusted by $|\det|^{t}$ and the Hecke eigenvalues by $\mathrm{N}v^{-t}$ (and $\mathrm{N}v^{-2t}$ for the central eigenvalues). It is used in the archimedean compatibility of cubic base change at the level of eigensystem classes in the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_archOccursInClassOf_whittakerCoefficient_fibre_eq_archW_twist_of_archOccursInClassOf_rat.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open NumberField.TateGlobal
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

theorem LanglandsTunnell.archOccursInClassOf_whittakerCoefficient_fibre_eq_archW_twist_of_archOccursInClassOf_rat
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd₁ : 0 < d₁)
    (Φ : HeckeEigensystem ℚ ℂ)
    (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (t : ℝ)
    (dR' : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR (P.twist (t : ℂ) 0))
    (hW' : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (g : Matrix (Fin 2) (Fin 2) ℝ),
      (dR' w hw).W g = (((|g.det| ^ t : ℝ)) : ℂ) * (dR w hw).W g)
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
                archW (fun _ _ => P) archC dR dC g * z)) :
    ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) (Φ.twist (fun v : HeightOneSpectrum (𝓞 ℚ) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))
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
                archW (fun _ _ => P.twist (t : ℂ) 0) archC dR' dC g * z) := by sorry
