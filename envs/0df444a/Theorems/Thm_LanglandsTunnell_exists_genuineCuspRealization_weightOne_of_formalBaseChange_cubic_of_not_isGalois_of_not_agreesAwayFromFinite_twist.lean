-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_genuineCuspRealization_weightOne_of_formalBaseChange_cubic_of_not_isGalois_of_not_agreesAwayFromFinite_twist
-- name    : LanglandsTunnell.exists_genuineCuspRealization_weightOne_of_formalBaseChange_cubic_of_not_isGalois_of_not_agreesAwayFromFinite_twist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/e4d8bd34-2fda-5246-9943-f242193cbadb
-- title:
--   Weight-one holomorphic descent along a non-Galois cubic base change
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$ which is not Galois over $\mathbb{Q}$, its ring of integers being an integral $\mathcal{O}_{\mathbb{Q}}$-algebra. Fix reals $c,u,d_1,d_2$ with $0<c$, $0<d_1$, $d_1<d_2$ and a finite set $T\subset \mathrm{GL}_2(\mathbb{A}_K)$ such that the union $D_K$ of the right translates $\mathfrak{S}_K(c,u,d_1,d_2)\,x$, $x\in T$, of the centre-cut Siegel set (those $g$ whose finite component lies in the integral subgroup `finiteIntegralGL2`, whose local height at every infinite place is at least $c$, whose window quantity `xWindowSq` at every infinite place is at most $u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$) satisfies `CoversModCentre`: every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ can be written with $\gamma\in\mathrm{GL}_2(K)$ and a central adelic scalar $z$ so that $\gamma g z\in D_K$. Fix analogous data $c',u',d_1',d_2',T'$ over $\mathbb{Q}$, with $0<c'$, $0<d_1'$, $d_1'<d_2'$ and the corresponding covering property for $D_{\mathbb{Q}}$. Throughout, the carrier pins are `productionPinsOf` for the respective domain: Borel structures with Haar measure on $\mathrm{GL}_2$ of the adeles, full central subgroup, level subgroups $N\mapsto\,$`levelOne` $N$ intersected with the kernel of the archimedean projection, Hecke generators `heckeGen` at each finite place, and the adelic additive Haar measure conditioned to `adelicBox`. Let $\Phi$ be a complex Hecke eigensystem over $\mathbb{Q}$ (a nonzero level ideal together with families $a,b$ of complex coefficients indexed by the height-one primes) such that the rescaled system $\Phi$`.toRawCentral` (the same $a$, with $b_v$ divided by the absolute norm of $v$) admits a smooth cuspidal realization on the pins for $D_{\mathbb{Q}}$ whose underlying function is continuous. Let $\Psi$ be a Hecke eigensystem over $K$ whose coefficients agree with those of `formalBaseChange` $\mathbb{Q}$ $K$ $\Phi$ (level $\top$, $a_{\mathfrak P}$ given by the Satake recursion `satakePow` in the inertia degree of $\mathfrak P$, and $b_{\mathfrak P}$ the corresponding power of $b$) outside a finite set of primes. Let $S_0$ be a finite set of height-one primes of $\mathcal{O}_{\mathbb{Q}}$ and $\chi$ a complex-valued function on these primes with $\chi(v)^2=1$ for $v\notin S_0$, and, for $v\notin S_0$, $\chi(v)=1$ precisely when no prime $\mathfrak P$ of $\mathcal{O}_K$ above $v$ has inertia degree $2$; assume $\Phi$ does not agree away from a finite set with its twist $\Phi$`.twist` $\chi$ (coefficients $\chi(v)a_v$ and $\chi(v)^2b_v$). Assume finally that $\Psi$`.toRawCentral` admits a smooth cuspidal realization $R$ on the pins for $D_K$ which is continuous, satisfies the predicate `HasArchCharacterAt₀` for the weight-one character `archWeightOneAt` at every real infinite place of $K$, and is `IsArchHolomorphicAt` at every real infinite place (for each $g$, the function $z\mapsto (\operatorname{Im} z)^{-1}R(g\cdot\iota_w(\text{Iwasawa section}(z)))$ is differentiable on the upper half-plane). Then $\Phi$`.toRawCentral` admits a smooth cuspidal realization on the pins for $D_{\mathbb{Q}}$ which is continuous, satisfies `HasArchCharacterAt₀` for the weight-one character at every real infinite place of $\mathbb{Q}$, and is archimedean-holomorphic there.
--
--   This is the descent step in the Langlands–Tunnell input: the weight-one holomorphic archimedean type of a realization over a non-Galois cubic field is transported back to the rational eigensystem, under the hypothesis that the rational system is not isomorphic away from finitely many places to its twist by the quadratic character recording inertia degree $2$ in the cubic field. It is used by [`LanglandsTunnell.exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre`](thm.html#LanglandsTunnell.exists_agreesLiftTraceSeed_isCusp_pair_of_detDictionaryRow_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_genuineCuspRealization_weightOne_of_formalBaseChange_cubic_of_not_isGalois_of_not_agreesAwayFromFinite_twist.lean

import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
open AutomorphicForm.SiegelCovering

theorem LanglandsTunnell.exists_genuineCuspRealization_weightOne_of_formalBaseChange_cubic_of_not_isGalois_of_not_agreesAwayFromFinite_twist
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] (hK : ¬ IsGalois ℚ K) (hdeg : Module.finrank ℚ K = 3)
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (hc : 0 < c)
    (hd₁ : 0 < d₁)
    (c' u' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd' : d₁' < d₂')
    (hcov' : CoversModCentre ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂'))
    (hc' : 0 < c')
    (hd₁' : 0 < d₁')
    (Φ : HeckeEigensystem ℚ ℂ)
    (hΦ : IsArithGenuineCuspRealizable ℚ
      (productionPinsOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂')
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      Φ)
    (Ψ : HeckeEigensystem K ℂ) (hagree : Ψ.AgreesAwayFromFinite (formalBaseChange ℚ K Φ))
    (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (χ : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (_hχ2 : ∀ v ∉ S₀, χ v * χ v = 1)
    (_hlink : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₀ →
      (χ v = 1 ↔ ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓.under (𝓞 ℚ) = v →
        (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal ≠ 2))
    (_hnd : ¬ HeckeEigensystem.AgreesAwayFromFinite Φ (Φ.twist χ))
    (hΨ : ∃ R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Ψ.toRawCentral,
      IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Ψ.toRawCentral R ∧
      (∀ w : InfinitePlace K, ∀ hw : w.IsReal, HasArchCharacterAt₀ K w (archWeightOneAt hw) R.toFun) ∧
      (∀ w : InfinitePlace K, ∀ hw : w.IsReal, IsArchHolomorphicAt w hw R.toFun)) :
    ∃ R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂')
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      Φ.toRawCentral,
      IsGenuineCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T', (· * x) '' centreCutSiegelSet ℚ c' u' d₁' d₂')
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      Φ.toRawCentral R ∧
      (∀ w : InfinitePlace ℚ, ∀ hw : w.IsReal, HasArchCharacterAt₀ ℚ w (archWeightOneAt hw) R.toFun) ∧
      (∀ w : InfinitePlace ℚ, ∀ hw : w.IsReal, IsArchHolomorphicAt w hw R.toFun) := by sorry
