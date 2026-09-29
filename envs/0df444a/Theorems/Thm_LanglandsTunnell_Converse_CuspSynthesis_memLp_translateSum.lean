-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum
-- name    : LanglandsTunnell.Converse.CuspSynthesis.memLp_translateSum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/1bba717c-4215-5af8-993d-e6dcb64cfece
-- title:
--   Square-integrability of translate sums on a Siegel window
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $c>0$ and $d_1>0$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $K$; write $D=\bigcup_{x\in T}(\cdot\,x)(\Sigma)$ for the union of the right translates by $T$ of the centre-cut Siegel set $\Sigma$ with parameters $c,u,d_1,d_2$, let $\mu$ be the adelic Haar measure on $\mathrm{GL}_2$ of the adeles and $\nu$ the adelic additive Haar measure conditioned on the adelic box, these being the data packaged by `pinsOf c u d₁ d₂ T`. Let $\Pi$ be a Hecke eigensystem over $K$ with complex coefficients, $S$ a finite set of finite places, $\mathrm{archR}$, $\mathrm{archC}$ archimedean parameters at the real and complex places, $\mathrm{epsS}$ a family of characters of the local unit groups, and $\omega$ a character of the idele group which is trivial on principal ideles, continuous and unitary, unramified at every $v\notin S$, whose value at the uniformizer idele at each $v\notin S$ is $N(v)^{-1}\Pi.b(v)$, the $b$-coefficient at $v$ of the twist of $\Pi$ by $v\mapsto N(v)^{-1/2}$, and which at each real place $w$ satisfies `IsArchCompAt` with exponent the central exponent of $\mathrm{archR}\,w$ and integer the value of its central sign, and at each complex place with the central exponent and central twist of $\mathrm{archC}\,w$. Let $d$ be a `JLData` for $S$, $\mathrm{epsS}$, $\omega$, let $dR$, $dC$ be archimedean Whittaker data for the given parameters and $dF$ a finite Whittaker datum for $S$ and $\Pi$. Assume: the Whittaker series `jlSeries' d archR archC dR dC dF` takes equal values at $g$ and at $\gamma g$ whenever $\gamma\in\mathrm{GL}_2(K)$ and both $g$ and $\gamma g$ lie in `kZeroSet S d.m`; the datum $d$ is `IsJLNice` for $\Pi$ twisted by $v\mapsto N(v)^{-1/2}$ and the given archimedean parameters; and the extension `theForm d archR archC dR dC dF` of that series through the rational points off `kZeroSet S d.m` is continuous. Finally let $k_1,\dots,k_n$ lie in the kernel of the archimedean projection of $\mathrm{GL}_2$ of the adeles, let $c_1,\dots,c_n\in\mathbb{C}$, and assume that $F(g)=\sum_i c_i\,\mathrm{theForm}(g k_i)$ is cuspidal in the sense that for every $g$ the integral over the adeles, against $\nu$, of $F$ along the unipotent one-parameter family $x\mapsto\begin{pmatrix}1&x\\0&1\end{pmatrix}$ vanishes. Then $F$ belongs to $L^2$ for $\mu$ restricted to $D$.
--
--   This is the square-integrability half of the construction of an automorphic cuspidal realisation from converse-theorem data: the finite linear combination of finite-adelic translates of the extended Whittaker series, once known to be cuspidal, is shown to lie in $L^2$ on the Siegel window. It is used in the passage from `IsJLNice` data to an arithmetic genuine cusp realisation, via `exists_isArithGenuineCuspRealizable_of_isJLNice`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_CuspSynthesis_memLp_translateSum.lean

import Definitions.Def_LanglandsTunnell_JLSynthesis
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel
open LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.CuspSynthesis.memLp_translateSum
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (hωunr : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt ω v)
    (hωb : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ((ω (uniformizerIdele K v) : ℂˣ) : ℂ) =
        (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b v)
    (hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchCompAt K ω w (archR w hw).centralExponent ((archR w hw).centralSign.val : ℤ))
    (hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchCompAt K ω w (archC w hw).centralExponent (archC w hw).centralTwist)
    (d : JLData K S epsS ω)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), g ∈ kZeroSet S d.m →
        globalPoints (𝓞 K) K γ * g ∈ kZeroSet S d.m →
        jlSeries' d archR archC dR dC dF (globalPoints (𝓞 K) K γ * g) = jlSeries' d archR archC dR dC dF g)
    (hnice : IsJLNice K S epsS ω d
      (Pi.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) archR archC)
    (hcont : Continuous (theForm d archR archC dR dC dF))
    {n : ℕ}
    (ks : Fin n → AdelicGL2 (𝓞 K) K) (cs : Fin n → ℂ) (hks : ∀ i, ks i ∈ finiteAdelicGL2Subgroup K)
    (hcusp : @IsCuspidalFn _ (pinsOf c u d₁ d₂ T).nS _ _ (pinsOf c u d₁ d₂ T).ν unipotentGL2
      (translateSum d archR archC dR dC dF ks cs)) :
    letI := (pinsOf c u d₁ d₂ T).mS
    MeasureTheory.MemLp (translateSum d archR archC dR dC dF ks cs) 2
      (((pinsOf c u d₁ d₂ T).μ).restrict (pinsOf c u d₁ d₂ T).D) := by sorry
