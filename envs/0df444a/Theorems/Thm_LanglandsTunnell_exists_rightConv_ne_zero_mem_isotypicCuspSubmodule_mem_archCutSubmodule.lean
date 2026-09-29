-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule
-- name    : LanglandsTunnell.exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/8bd5957e-931d-58ed-b2f1-cd8787b898f6
-- title:
--   Bi-finite isotypic smoothing of a continuous cuspidal realization
-- statement:
--   Fix real parameters $c,u,d_1,d_2$ and a finite set $T$ of elements of $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$, and let $D=\bigcup_{x\in T}\{g x: g\in \text{centreCutSiegelSet}\ \mathbb{Q}\ c\,u\,d_1\,d_2\}$ be the corresponding finite union of right translates of the centre-cut Siegel set (those $g$ whose finite part is integral, whose local heights at all infinite places are $\ge c$, whose $x$-window squares are $\le u^2$, and whose archimedean determinant norms lie in $[d_1,d_2]$). Assume $d_1<d_2$ and that $D$ satisfies `CoversModCentre`, i.e. every adelic $g$ can be moved into $D$ by a global point of $\mathrm{GL}_2(\mathbb{Q})$ on the left and a central adelic scalar on the right. Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with values in $\mathbb{C}$ (a nonzero level ideal together with families $a,b$ indexed by the finite places), and let $R$ be a smooth cuspidal realization of the raw-central rescaling $\Phi.\mathrm{toRawCentral}$ (same level and same $a$, with $b_v$ replaced by $b_v$ divided by the absolute norm of $v$) at the production pins attached to $D$, namely Haar measure and the Borel structure on the adelic $\mathrm{GL}_2$, full central subgroup, the level subgroups $N\mapsto \text{levelOne}\ N\sqcap\text{finiteAdelicGL2Subgroup}$, the Hecke generators $v\mapsto \text{heckeGen}\ v$, and the adelic box conditioned additive Haar measure on the adeles; thus $R$ carries a nowhere identically zero function $R.\mathrm{toFun}$, a central character $R.\mathrm{centralChar}$, smooth cuspidality, invariance under right translation by the level subgroup at $\Phi.\mathrm{level}$, and Hecke and central eigenvalue relations with eigenvalues $a_v$ and the rescaled $b_v$ outside a finite exceptional set. Assume finally that $R.\mathrm{toFun}$ is continuous. Then there exist a finite set $S$ of finite places of $\mathbb{Q}$, an archimedean type family $tys$ (for each infinite place $w$ a finite list of finite-dimensional complex representations of the row-isometry subgroup of $w$'s completion), and a function $f$ on the adelic $\mathrm{GL}_2$ such that: $S$ contains the exceptional set of $R$; $f$ is a factorizable test function, that is a product of a compactly supported archimedean factor smooth in the matrix entries with a compactly supported locally constant finite factor; $f$ is archimedean bi-finite for $tys$, meaning $x\mapsto f(x^{-1})$ lies in the archimedean cut submodule of $tys$ and $f$ lies in the archimedean dual cut submodule; the right convolution $g\mapsto\int R.\mathrm{toFun}(gx)f(x)\,dx$ against Haar measure is not the zero function; this convolution lies in the isotypic cuspidal submodule, the span of the continuous smooth cuspidal automorphic functions with central character $R.\mathrm{centralChar}$ that are invariant under the level subgroup at $\Phi.\mathrm{level}$ and are Hecke coset eigenfunctions with eigenvalue $a_v$ and central eigenfunctions with eigenvalue $b_v$ divided by the absolute norm of $v$, for all $v\notin S$; and this convolution lies in the archimedean cut submodule of $tys$.
--
--   This is the smoothing step for adelic automorphic forms: a continuous cuspidal realization of a Hecke eigensystem is replaced, without losing non-triviality or the eigenvalue conditions away from a finite set of places, by its right convolution with a factorizable test function that is finite for a prescribed family of archimedean types. It feeds the construction of an irreducible $\mathrm{GL}_2$-subrepresentation inside the span of translates of a realization, and the production of an archimedean Casimir eigenvector of minimal weight, on the way to the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField
open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem LanglandsTunnell.exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (_hd : d₁ < d₂) (_hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Φ.toRawCentral)
    (hR : Continuous R.toFun) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (tys : ArchTypeFamily ℚ) (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      R.exceptionalSet ⊆ S ∧ IsFactorizableTestFn ℚ f ∧ IsArchBiFinite ℚ tys f ∧
        rightConv ℚ R.toFun f ≠ 0 ∧
        rightConv ℚ R.toFun f ∈ isotypicCuspSubmodule ℚ
          (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
            (adelicBox ℚ))
          R.centralChar Φ.level S Φ ∧
        rightConv ℚ R.toFun f ∈ archCutSubmodule ℚ tys := by sorry
