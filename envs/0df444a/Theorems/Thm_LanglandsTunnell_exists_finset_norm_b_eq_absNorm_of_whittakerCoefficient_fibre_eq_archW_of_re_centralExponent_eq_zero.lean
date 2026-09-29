-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_finset_norm_b_eq_absNorm_of_whittakerCoefficient_fibre_eq_archW_of_re_centralExponent_eq_zero
-- name    : LanglandsTunnell.exists_finset_norm_b_eq_absNorm_of_whittakerCoefficient_fibre_eq_archW_of_re_centralExponent_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/9131b12f-5da5-5f92-a080-41d8bf9b9448
-- title:
--   Unitary archimedean datum forces ‖bₚ‖ = Np almost everywhere
-- statement:
--   Let $c,u,d_1,d_2$ be reals with $d_1<d_2$, let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and put $D=\bigcup_{x\in T}\{g x : g\in \mathfrak{S}\}$, where $\mathfrak{S}=$ `centreCutSiegelSet ℚ c u d₁ d₂` consists of the $g$ whose finite part is integral, whose archimedean components satisfy $c\le$ `localHeight` and `xWindowSq` $\le u^2$ at every infinite place, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for every $w$; assume `CoversModCentre`, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(\mathbb{Q})$ and a central idelic scalar $z$ with $\gamma g z\in D$. Let $\Phi$ be a complex Hecke eigensystem over $\mathbb{Q}$ (a nonzero level ideal together with families $a,b$ indexed by the primes), let $P$ be a real archimedean parameter, let `archC` assign a complex archimedean parameter to each complex place, and let $dR$, $dC$ be archimedean Whittaker data for $P$ at each real place and for `archC` at each complex place. Assume `ArchOccursInClassOf`: some eigensystem agreeing with $\Phi$ outside a finite set of primes admits, after passing to its raw central normalisation $b_v\mapsto (\mathrm{cNorm}\,v)^{-1}b_v$, a smooth cusp realisation $R'$ at the production pins of $D$ (Haar measures on $\mathrm{GL}_2(\mathbb{A})$ and on $\mathbb{A}$ conditioned to `adelicBox`, full central subgroup, level subgroups `levelOne N ⊓ finiteAdelicGL2Subgroup`, Hecke generators `heckeGen v`) which is genuine, i.e. $R'$ is continuous, and whose function $\varphi=R'.\mathrm{toFun}$ satisfies: there is $g_0$ such that the Whittaker coefficient of $\varphi$ at $\alpha=1$ against the standard additive character of $\mathbb{A}_{\mathbb{Q}}$ is nonzero at some $g$ with the same finite part as $g_0$, and there is $z\in\mathbb{C}$ with $W_\varphi(g)=\bigl(\prod_w \mathrm{archDetNorm}_w(g)^{\,\mathrm{mult}\,w}\bigr)^{-1/2}\,\mathrm{archW}(P,\mathrm{archC},dR,dC)(g)\,z$ for every $g$ with finite part that of $g_0$. Assume finally that the central exponent of $P$ is purely imaginary, $\mathrm{Re}\,(\mathrm{centralExponent}\,P)=0$. Then there is a finite set $S_0$ of primes of $\mathbb{Z}$ such that $\|\Phi.b\,p\| = \mathrm{N}(p)$ for every prime $p\notin S_0$.
--
--   This records the unitary normalisation of a Hecke eigensystem: once the archimedean part of a cuspidal realisation in the class of $\Phi$ is pinned to an archimedean Whittaker datum whose central quasi-character has trivial modulus, the central Hecke eigenvalues $b_p$ have absolute value equal to the norm of $p$ at almost all primes. It is used in the Langlands–Tunnell route as the normalisation input to the converse-theorem steps that produce an arithmetically normalised weight-one cuspidal constituent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_finset_norm_b_eq_absNorm_of_whittakerCoefficient_fibre_eq_archW_of_re_centralExponent_eq_zero.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open NumberField.TateGlobal
open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse

theorem LanglandsTunnell.exists_finset_norm_b_eq_absNorm_of_whittakerCoefficient_fibre_eq_archW_of_re_centralExponent_eq_zero
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂)
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
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S₀ →
      ‖Φ.b p‖ = (Ideal.absNorm p.asIdeal : ℝ) := by sorry
