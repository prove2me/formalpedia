-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_archOccursInClassOf_archCasimirAt_laplaceEigenvalue_of_whittakerCoefficient_fibre_eq
-- name    : LanglandsTunnell.exists_archOccursInClassOf_archCasimirAt_laplaceEigenvalue_of_whittakerCoefficient_fibre_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/fb24c09e-96c0-5f87-91e4-64c7d24f922c
-- title:
--   Casimir eigenvalue from a Whittaker factorisation on one finite fibre
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite set of elements of $\mathrm{GL}_2(\mathbb{A}_K)$; write $D=\bigcup_{x\in T}\{g x : g\in \mathrm{centreCutSiegelSet}\ K\ c\ u\ d_1\ d_2\}$, where the centre-cut Siegel set consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean components satisfy $c\le \mathrm{localHeight}$ and $\mathrm{xWindowSq}\le u^2$ at every infinite place, and with $\mathrm{archDetNorm}_v(g)\in[d_1,d_2]$ for all infinite $v$. Assume `CoversModCentre K D`: every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and a central adelic scalar $z$ with $\gamma g z\in D$. Let $\Theta$ be a complex Hecke eigensystem over $K$ (a level ideal $\ne\bot$ together with families $a_v,b_v$), $w$ a real infinite place, $P$ a real archimedean parameter, and $W_\infty:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ a continuous function which is invariant under right multiplication by any $k$ with trivial archimedean component, which is smooth at $w$ in the sense of `IsArchSmoothAt` (each $e\mapsto W_\infty(g\cdot\mathrm{archRealLiftAt}\,e)$ is $C^\infty$ on invertible matrices) and which satisfies $\mathrm{archCasimirAt}\,W_\infty=\lambda(P)\cdot W_\infty$, where $\lambda(P)=1/4-((u_1-u_2)/2)^2$ in the principal case and $(1-k^2)/4$ in the discrete case. Assume finally `ArchOccursInClassOf K D Θ` for the following property: some Hecke eigensystem $\Theta'$ agreeing with $\Theta$ away from a finite set of primes carries a continuous smooth cusp realisation $R$ at the production pins of $D$ (level subgroups $\mathrm{levelOne}\,N\sqcap\mathrm{finiteAdelicGL2Subgroup}$, Hecke generators $\mathrm{heckeGen}\,v$, additive measure conditioned to `adelicBox`) for $\Theta'.\mathrm{toRawCentral}$, such that there is $g_0$ with: the Whittaker coefficient of $R$ at $\alpha=1$ against the standard additive character of $\mathbb{A}_K$, namely $g\mapsto\int R(u(x)g)\,\psi(-x)$, is non-zero at some $g$ with $g_f=g_{0,f}$, and there is a constant $z\in\mathbb{C}$ with $W_R(g)=\bigl(\prod_{v\mid\infty}\mathrm{archDetNorm}_v(g)^{m_v}\bigr)^{-1/2}W_\infty(g)\,z$ for every $g$ on that finite fibre. The conclusion: there is an integer $n$ such that `ArchOccursInClassOf K D Θ` holds for the property that the realising function $\varphi$ satisfies the weight-$n$ condition `HasArchCharacterAt₀` at $w$ for the character $(\mathrm{archWeightChar}_{\mathbb{R}}\,n)$ composed with `rowIsometrySubgroup₀Map` of the identification of $w$'s completion with $\mathbb{R}$, is smooth at $w$, and satisfies $\mathrm{archCasimirAt}\,\varphi=\lambda(P)\cdot\varphi$.
--
--   This transfers a prescribed archimedean parameter, given only through a Whittaker factorisation on a single finite fibre (the shape in which a converse theorem delivers its realisation), into an occurrence statement for the Hecke class on the Siegel window: the class is realised by a form of some integral weight $n$ at the real place $w$ whose Casimir eigenvalue at $w$ is the Laplace eigenvalue of the parameter. It is used in the Langlands–Tunnell part of the development, in particular in the identification of weight-zero behaviour under the long Weyl element and in the construction of the formal base-change class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_archOccursInClassOf_archCasimirAt_laplaceEigenvalue_of_whittakerCoefficient_fibre_eq.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell LanglandsTunnell.RealArchParam

theorem LanglandsTunnell.exists_archOccursInClassOf_archCasimirAt_laplaceEigenvalue_of_whittakerCoefficient_fibre_eq
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ) (w : InfinitePlace K) (hw : w.IsReal) (P : RealArchParam)
    (Warch : AdelicGL2 (𝓞 K) K → ℂ) (hWc : Continuous Warch)
    (hWfin : ∀ (g k : AdelicGL2 (𝓞 K) K), glArch (𝓞 K) K k = 1 → Warch (g * k) = Warch g)
    (hWs : IsArchSmoothAt hw Warch) (hWΩ : archCasimirAt hw Warch = (laplaceEigenvalue P) • Warch)
    (hWF : ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) Θ
        (fun φ => ∃ g₀ : AdelicGL2 (𝓞 K) K,
          (∃ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = glFin (𝓞 K) K g₀ ∧
            whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
              (NumberField.StandardAddChar.stdAddChar K) φ 1 g ≠ 0) ∧
          ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = glFin (𝓞 K) K g₀ →
            whittakerCoefficient K
              (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
              (NumberField.StandardAddChar.stdAddChar K) φ 1 g =
              (((∏ v : InfinitePlace K, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                Warch g * z)) :
    ∃ n : ℤ,
      ArchOccursInClassOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ K w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
          IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (laplaceEigenvalue P) • φ) := by sorry
