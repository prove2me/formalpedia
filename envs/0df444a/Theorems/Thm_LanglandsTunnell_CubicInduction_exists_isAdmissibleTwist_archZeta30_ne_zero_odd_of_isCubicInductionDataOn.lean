-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_ne_zero_odd_of_isCubicInductionDataOn
-- name    : LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_ne_zero_odd_of_isCubicInductionDataOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/10266ff9-1970-57ba-9747-3072b0b5b20a
-- title:
--   Odd admissible twist with non-vanishing archimedean GL₃ × GL₁ zeta
-- statement:
--   Throughout, $K$ is a number field of degree $3$ over $\mathbb{Q}$ (the hypothesis `hdeg` fixes $\operatorname{finrank}_{\mathbb{Q}} K = 3$), with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra.
--
--   **Character data.** $\psi$ is an additive character of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$, and `hψ` asserts that $\psi$ is a global additive character, i.e. trivial on principal adeles $\operatorname{algebraMap}_{\mathbb{Q}}(\alpha)$, continuous, and non-trivial. $\mu$ is a monoid homomorphism from the idele units of $K$ to $\mathbb{C}^\times$, and `hμ` asserts that $\mu$ is an admissible twist: trivial on principal ideles coming from $K^\times$, continuous, and of absolute value $1$ at every idele. Families $uR, aR$ (indexed by the real places of $K$, with values in $\mathbb{C}$ and in $\mathbb{Z}/2$) and $uC, kC$ (indexed by the complex places, with values in $\mathbb{C}$ and in $\mathbb{Z}$) record the archimedean type of $\mu$: `huR` states that at each real place $w$ the local archimedean component of $\mu$ is $x \mapsto \|x\|^{\mathrm{mult}(w) \, uR_w} \big(\iota_w(x)/\|x\|\big)^{(aR_w).\mathrm{val}}$, and `huC` the analogous identity at each complex place $w$ with exponents $uC_w$ and $kC_w$, where $\iota_w$ is the embedding of the completion at $w$ into $\mathbb{C}$. The hypothesis `hlev` requires the local component $\mathrm{psiLoc}\,\psi\,v$ of $\psi$ to have level $0$ at every finite place $v$ of $\mathbb{Q}$, the level being the supremum of the integers $n$ such that $\psi$ kills the set of $x$ with $v(x) \le \exp n$. The hypothesis `hns` states that $\mu$ is not of norm type: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $K$ at which $\mu$ is unramified and with $\eta$ unramified at the prime $\mathfrak{p}$ of $\mathbb{Q}$ below it, $\mu$ evaluated at the uniformiser idele at $\mathfrak{P}$ equals $\eta$ evaluated at the uniformiser idele at $\mathfrak{p}$, raised to the inertia degree of $\mathfrak{P}$ over $\mathfrak{p}$.
--
--   **Carrier data and the cubic induction datum.** A set $D$ of adelic $GL_2$-matrices, a family $U$ of subgroups indexed by ideals of $\mathcal{O}_{\mathbb{Q}}$ and a family $\mathrm{gen}$ of adelic $GL_2$-matrices indexed by finite places assemble, through `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)`, into carrier pins whose measures are the Borel structure and Haar measure on adelic $GL_2$, whose central subgroup is $\top$, and whose additive measure is adelic Haar measure conditioned on the adelic box. $S$ is a finite set of finite places of $\mathbb{Q}$ which, by `hS`, consists exactly of the bad places for $(K,\mu)$, a place being bad when it is ramified in $K$ or $\mu$ is twist-ramified above it. $X$ is a `CubicInductionData`, that is, a tuple consisting of a function `X.form` on adelic $GL_3$ over $\mathbb{Q}$, its Whittaker function `X.whittaker`, local Whittaker functions `X.whittakerLoc v` on $GL_3$ of the completion at each finite place $v$, an archimedean Whittaker function `X.whittakerArch` on $GL_3$ of the infinite adele ring, a central character `X.centralChar` on the idele units of $\mathbb{Q}$, and a dual Whittaker function `X.dualWhittaker`. The hypothesis `hX` asserts `IsCubicInductionDataOn K` for these pins, $\psi$, $\mu$, $S$ and $X$; its twenty-one clauses are summarised here: left invariance of `X.form` under $GL_3(\mathbb{Q})$, transformation by `X.centralChar` under adelic central scalars, the idele class property of `X.centralChar`, cuspidality along the two maximal parabolics $P_{21}$ and $P_{12}$, the identification of `X.whittaker` with the $\psi$-Whittaker transform of `X.form` together with the $\psi$-Whittaker transformation law $W(u(x,y,z)g) = \psi(x+y)W(g)$, the mirabolic Fourier expansion of `X.form` by `X.whittaker`, the local Whittaker laws for $\mathrm{psiLoc}\,\psi\,v$, factorisation of `X.whittaker` into `X.whittakerArch` at the archimedean component times the product of the local factors over any finite set containing $S$ outside which the component lies in the maximal compact subgroup, induced sphericity of the local factors off $S$ in terms of the induced coefficients of $\mu$, invariance of the local factors off $S$ at places unramified in $K$ under the congruence subgroup of level $\mathrm{inducedLevelAt}\,K\,\mu\,v$, local Whittaker multiplicity one, moderate growth of `X.form`, $K$-finiteness of `X.whittakerArch`, the iota-moment and Whittaker half-plane conditions, and the corresponding statements for `X.dualWhittaker` relative to $\psi^{-1}$ and the dual form.
--
--   **Analytic hypotheses on $X$.** `hcont`, `hcontW` and `hcontW'` require `X.form`, `X.whittaker` and `X.dualWhittaker` to be continuous. `hW` and `hW'` require `X.whittaker` and `X.dualWhittaker` to be gauge-majorised: there are an exponent $t$, a finite set $T$ of finite places and a bound $B$ such that the function vanishes off the corresponding root level, and on it satisfies, for each $N$, a bound $C/\big(\mathrm{rootSizeProd}(g)^t (1+\mathrm{archRootSum}(g))^N\big)$. `hne` requires `X.whittakerArch` to be not identically zero. The hypothesis `hatS` imposes, at each $w \in S$, four conditions on $W_w =$ `X.whittakerLoc w`: $W_w(1) = 1$; every non-zero $F$ in the cyclic subspace generated by $W_w$ under right translation has $W_w$ in its own cyclic subspace; some open subgroup $U_w$ of $GL_3$ of the completion fixes $W_w$ under right translation; and for every open subgroup $U_w$ there is a finite set $B$ of functions whose complex span contains every right $U_w$-invariant element of the cyclic subspace of $W_w$. The hypothesis `hcent` requires, at each $w \in S$, that the local component of `X.centralChar` at $w$ have absolute value $1$ on $(\mathbb{Q}_w)^\times$ and that $W_w$ transform by it under multiplication by scalar matrices. The hypothesis `hωcond` requires, at every finite place $v$ of $\mathbb{Q}$ not ramified in $K$, the existence of $a \le \mathrm{inducedLevelAt}\,K\,\mu\,v$ which is a conductor exponent at $v$ for the local component of `X.centralChar`.
--
--   **Archimedean furniture.** $E$ is a monoid homomorphism from the units of the infinite adele ring of $\mathbb{Q}$ to the idele units, and `hE` asserts that it is a section supported at infinity: the infinite part of $E u$ is $u$ and its finite part is $1$. A non-zero rational $a$ is fixed, together with a unit $a_\infty$ of the infinite adele ring whose underlying element is the image of $a$, and the additive character $\psi_\infty$ given by $\psi_\infty(x) = \mathrm{psiArch}(a x)$; `hψinf` requires the restriction of $\psi$ along the inclusion of the infinite adeles to be $\psi_\infty$. The measure $\nu_{\mathrm{add}}$ on the infinite adele ring is $|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the identification with the mixed space, and $\nu_{\mathrm{mul}}$ is a Haar measure on the units of the infinite adele ring.
--
--   **The archimedean package `hArch`.** This hypothesis is the conjunction of five items. First, `X.whittakerArch` is continuous and there is $t \in \mathbb{N}$ such that for every $N$ there is $C$ with $\|$`X.whittakerArch`$(g_\infty)\| \le C/\big((\prod_w \mathrm{archRoot}_1(w,g)\,\mathrm{archRoot}_2(w,g))^t (1+\mathrm{archRootSum}(g))^N\big)$ for all adelic $g$, where $g_\infty$ is the archimedean component of $g$. Second, `X.whittakerArch` satisfies the $\psi_\infty$-Whittaker law. Third, it transforms under archimedean central scalars $z$ by the factor `X.centralChar` $(E z)$. Fourth, for every admissible twist $\sigma$ of $\mathbb{Q}$, every $t \in \mathbb{C}$ and $e \in \mathbb{Z}$ such that $\sigma$ has archimedean type $(t,e)$ at every real place of $\mathbb{Q}$, and every $g_\infty \in GL_3$ of the infinite adele ring, there is an entire function $P$ such that: (i) for some $\sigma_0$ the $GL_3 \times GL_1$ integral $\mathrm{archZeta30}$ of $h \mapsto$ `X.whittakerArch`$(h\,g_\infty)$ against $\sigma \circ E$ converges for $\operatorname{Re} s > \sigma_0$ and equals $P(s)$ times the archimedean factor of the Hecke datum $\mathrm{heckeDatum}\,K\,\mu$ with parameters $(uR + t, aR + e \bmod 2, uC + t, kC)$; (ii) in every vertical strip $P$ satisfies a bound $C \exp(A|\operatorname{Im} s|)$; (iii) in every vertical strip and for every $N$ the product of $|\operatorname{Im} s|^N$ with $\|P(s)\|$ times the same archimedean factor is bounded for $|\operatorname{Im} s|$ large; and (iv) for some $\sigma_1$ the dual integral $\mathrm{archZeta31}$ of $\mathrm{dualWhittakerFn3}$ of $h \mapsto$ `X.whittakerArch`$(h\,g_\infty)$ against $(\sigma \circ E)^{-1}$ at $\mathrm{weylPrime3} \cdot \mathrm{transposeInv3}\,1$ converges in the relevant half-plane, and for $\operatorname{Re}(1-s) > \sigma_1$ the dual zeta $\mathrm{archZetaDual31}$ at $1-s$ equals the product of the archimedean root-number factors $\prod_{w \text{ real}} \mathrm{signEpsilon}(aR_w + e)$, $\prod_{w \text{ complex}} i^{|kC_w|}$ and $\prod_w \mathrm{lambdaArch}\,K\,w$ (this last factor being $1$ at real places and $i$ at complex places), times `X.centralChar`$(E a_\infty) \cdot \sigma(E a_\infty)^3$, times $|a|^{3(s-1/2)}$, times $P(s)$, times the dual archimedean factor of the same Hecke datum at $1-s$. Fifth, there exist an admissible twist $\sigma$ of $\mathbb{Q}$ and a point $s$ at which $\mathrm{archZeta30}\,\nu_{\mathrm{mul}}$ of `X.whittakerArch` against $\sigma \circ E$ at $g = 1$ is non-zero.
--
--   **Conclusion.** Under these hypotheses there exist $g_\infty \in GL_3$ of the infinite adele ring of $\mathbb{Q}$ and a monoid homomorphism $\sigma$ from the idele units of $\mathbb{Q}$ to $\mathbb{C}^\times$ such that:
--
--   (1) $\sigma$ is an admissible twist of $\mathbb{Q}$, i.e. trivial on principal ideles, continuous and unitary;
--
--   (2) there are $t \in \mathbb{C}$ and $e \in \mathbb{Z}$ with $\sigma$ of archimedean type $(t,e)$ at every real place $w$ of $\mathbb{Q}$, in the sense of `IsArchCompAt ℚ σ w t e`, and $(-1)^e = -1$ in $\mathbb{C}$, so that $e$ is odd;
--
--   (3) for every real number $\sigma_0$ there is $s \in \mathbb{C}$ with $\operatorname{Re} s > \sigma_0$ and
--   $$\int_{(\mathbb{A}_{\mathbb{Q},\infty})^\times} \mathrm{X.whittakerArch}\big(\iota(\mathrm{diag}(h,1))\,g_\infty\big)\, \sigma(E h)\, \|h\|^{s-1}\, d\nu_{\mathrm{mul}}(h) \ne 0,$$
--   that is, $\mathrm{archZeta30}\,\nu_{\mathrm{mul}}$ of the right translate $h \mapsto$ `X.whittakerArch`$(h\,g_\infty)$ against $\sigma \circ E$, evaluated at $s$ and at $g = 1$, is non-zero.
--
--   This is the archimedean non-vanishing input, in its odd-twist form, for the converse-theorem step of the Langlands–Tunnell argument: it produces an admissible idele class character of $\mathbb{Q}$ whose archimedean exponent at the real place is odd and a translate for which the archimedean $GL_3 \times GL_1$ zeta integral is non-zero at points arbitrarily far to the right. It is used in the analysis of the local dual zeta integrals of the cubic induction datum at the bad places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_ne_zero_odd_of_isCubicInductionDataOn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg
  LanglandsTunnell.CubicLambda

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_ne_zero_odd_of_isCubicInductionDataOn
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      (S : Set (HeightOneSpectrum (𝓞 ℚ))) X)
    (hcont : Continuous X.form) (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hne : X.whittakerArch ≠ 0)
    (hatS : ∀ w ∈ S, X.whittakerLoc w 1 = 1 ∧
      (∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w), F ≠ 0 → X.whittakerLoc w ∈ gl3CyclicSubspace F) ∧
      (∃ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) ∧
        ∀ k ∈ Uw, ∀ g : LocalGL3 w, X.whittakerLoc w (g * k) = X.whittakerLoc w g) ∧
      ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
        ∃ B : Finset (LocalGL3 w → ℂ), ∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w),
          (∀ k ∈ Uw, ∀ g : LocalGL3 w, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)))
    (hcent : ∀ w ∈ S,
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h)
    (hωcond : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsRamifiedIn K v → ∃ a ≤ inducedLevelAt K μ v,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar X.centralChar v) a)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (ha : a ≠ 0) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (hψinf : ψ.compAddMonoidHom
        (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = psiInf)
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (hArch :
      (Continuous X.whittakerArch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) ∧
      IsGL3PsiWhittakerFn psiInf X.whittakerArch ∧
      (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        X.whittakerArch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((X.centralChar (E z) : ℂˣ) : ℂ) * X.whittakerArch g) ∧
      (∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
        ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
        ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
          (∃ σ₀ : ℝ, IsArchZeta30ConvergentAbove ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) 1 σ₀ ∧
            ∀ s : ℂ, σ₀ < s.re →
              archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 =
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s) ∧
          (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ‖P s‖ ≤ C * Real.exp (A * |s.im|)) ∧
          (∀ (σ₁ σ₂ : ℝ) (N : ℕ), ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
            |s.im| ^ N *
              ‖P s *
                (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                  (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s‖ ≤ C) ∧
          (∃ σ₁ : ℝ, IsArchZeta31ConvergentAbove ν_mul ν_add (dualWhittakerFn3 (fun h => X.whittakerArch (h * gInf)))
              (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
            ∀ s : ℂ, σ₁ < (1 - s).re →
              archZetaDual31 ν_mul ν_add (fun h => X.whittakerArch (h * gInf)) (σ.comp E) (1 - s) 1 =
                (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
                    fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
                  ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                      fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
                  ∏ w : InfinitePlace K, lambdaArch K w) *
                (((X.centralChar (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul X.whittakerArch (σ.comp E) s 1 ≠ 0)

 :
    ∃ (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), IsAdmissibleTwist ℚ σ ∧
      (∃ (t : ℂ) (e : ℤ), (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t e) ∧ (-1 : ℂ) ^ e = -1) ∧
      ∀ σ₀ : ℝ, ∃ s : ℂ, σ₀ < s.re ∧ archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 ≠ 0 := by sorry
