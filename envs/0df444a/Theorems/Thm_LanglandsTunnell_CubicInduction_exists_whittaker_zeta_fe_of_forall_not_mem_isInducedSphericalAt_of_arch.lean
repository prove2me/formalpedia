-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_whittaker_zeta_fe_of_forall_not_mem_isInducedSphericalAt_of_arch
-- name    : LanglandsTunnell.CubicInduction.exists_whittaker_zeta_fe_of_forall_not_mem_isInducedSphericalAt_of_arch
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/94747d54-a3fa-5c23-be98-0a9b826241e7
-- title:
--   Converse-theorem input for the cubic induction from an archimedean Whittaker vector
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$ (`hdeg`), equipped with an algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$ which is integral, and let $\mu$ be a character of the idele group $(\mathbb{A}_K)^\times$ with values in $\mathbb{C}^\times$ satisfying `IsAdmissibleTwist K μ` (`hμ`), i.e. $\mu$ is trivial on the principal ideles $K^\times$, continuous, and of absolute value $1$ everywhere.
--
--   The hypothesis `hns` asserts non-descent of $\mu$ to $\mathbb{Q}$: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that, at every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified (in the sense that the local component `localChar μ 𝔓` is trivial on the units of the valuation ring) and above which the prime $\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ is unramified for $\eta$, the value of $\mu$ on the uniformizer idele at $\mathfrak{P}$ equals the value of $\eta$ on the uniformizer idele at $\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ raised to the inertia degree of $\mathfrak{P}$.
--
--   Additive data: $\psi$ is an additive character of $\mathbb{A}_{\mathbb{Q}}$ with `IsGlobalAddChar ℚ ψ` (`hψ`), i.e. trivial on $\mathbb{Q}$, continuous, and non-trivial; and `hψS` requires that the local component $\psi_v$ (the pullback of $\psi$ along the embedding of $\mathbb{Q}_v$ into the adeles at $v$) has `addCharLevel` equal to $0$ for every finite place $v$.
--
--   A finite set $S$ of primes of $\mathcal{O}_{\mathbb{Q}}$ is given, and `hS` identifies $S$ as exactly the set of bad places of the induction: $v\in S$ iff either some prime of $K$ above $v$ is ramified, or $\mu$ ramifies at some prime of $K$ above $v$.
--
--   A family `Wfin` of complex functions on the local groups $\mathrm{GL}_3(\mathbb{Q}_v)$ is given, and `hfin` requires that for $v\notin S$ the function `Wfin v` is a $\psi_v$-Whittaker function (i.e. $W(u(x,y,z)g)=\psi_v(x+y)W(g)$ for upper unipotent $u(x,y,z)$), satisfies `IsInducedSphericalAt (inducedCoeff K μ) v` for the standard maximal compact $\mathrm{GL}_3(\mathbb{Z}_v)$ — that is: right invariance under that subgroup, the Hecke eigenvalue equations with eigenvalues $\mathrm{N}v\cdot e_1$ and $\mathrm{N}v\cdot e_2$ for the two generators $\mathrm{diag}(\varpi,1,1)$, $\mathrm{diag}(\varpi,\varpi,1)$, and the central relation with eigenvalue $e_3$, where $e_1,e_2,e_3$ are the first three induced coefficients of the Euler polynomial $\prod_{\mathfrak{P}\mid v}(1-c(\mathfrak{P})X^{f(\mathfrak{P})})$ formed from `inducedCoeff K μ` — is normalised by `Wfin v 1 = 1`, and has the prescribed spherical torus values `HasSphericalTorusValuesAt`.
--
--   A character $\omega$ of $(\mathbb{A}_{\mathbb{Q}})^\times$ is given together with `hω`, which has three parts: $\omega$ is an admissible twist of $\mathbb{Q}$; at every prime $p$ which is not a bad place, $\omega$ is unramified and its Euler coefficient equals the third induced coefficient `inducedE3 ℚ (inducedCoeff K μ) p`; and for every system of archimedean parameters $(u_R,a_R)$ at the real places and $(u_C,k_C)$ at the complex places of $K$ realising the archimedean components of $\mu$ in the sense of `IsArchCompAt`, the real place of $\mathbb{Q}$ has archimedean component of $\omega$ given by the exponent $\sum_{w\ \mathrm{real}}u_R(w)+\sum_{w\ \mathrm{complex}}2u_C(w)$ and the integer $\sum_{w\ \mathrm{real}}a_R(w)+\sum_{w\ \mathrm{complex}}(k_C(w)+1)$.
--
--   The hypothesis `hloc` supplies the local data at the bad places: for every $v\in S$ and every unit complex number $\theta$ there exist three locally constant characters $\nu_0,\nu_1,\nu_2$ of $\mathbb{Q}_v^\times$ and conductor exponents $a_0,a_1,a_2\ge 1$ with $\sum_i a_i$ equal to $\sum_{\mathfrak{P}\mid v} f(\mathfrak{P})\cdot$`pinnedExp K μ 𝔓` (the conductor exponent of the local component of $\mu$ plus the level of the standard local additive character), with each $|\nu_i(\varpi_v)|=1$, with $\nu_0\nu_1\nu_2$ equal to the local component of $\omega$ at $v$, with $\prod_i L_v(\nu_i,s)$ equal to the inverse of the induced Euler polynomial evaluated at $(\mathrm{N}v)^{-s}$, and with $\prod_i\varepsilon_v(\nu_i,1/2)=\theta$; and moreover there is a floor $a_0$ such that for every level $c\ge a_0$ there is a local function $W$ on $\mathrm{GL}_3(\mathbb{Q}_v)$ with $W(1)=1$, which is a Whittaker function for the standard local additive character, is right invariant under some open subgroup, is congruence-equivariant at every level $m\ge\sum_i a_i$ for the local component of $\omega$, has vanishing unipotent integral, satisfies a support-and-majorant bound in terms of `detSize`, `lastRowSup` and `minorSup`, transforms under central scalars $z$ by the local component of $\omega$, and whose twisted local zeta integrals satisfy, for every unramified unitary $\chi$ and every $g$ in `converseCongruenceSet3 v c`, a local functional equation: there are a function $P$ of the form $Q((\mathrm{N}v)^{-s})(\mathrm{N}v)^{ms}$, abscissae $\sigma_0,\sigma_1$ with the corresponding convergence statements for `localZeta30` and for the dual integral, with `localZeta30` equal to $\prod_i L_v(\nu_i\chi,s)\cdot P(s)$ in the right half-plane, and with `localZetaDual31` at $1-s$ equal to $\prod_i L_v((\nu_i\chi)^{-1},1-s)$ times $\prod_i\varepsilon_v(\nu_i\chi,1/2)$ times $(\mathrm{N}v)^{(\sum_i a_i)(1/2-s)}$ (the $a_i$ being conductor exponents of the $\nu_i\chi$) times $P(s)$.
--
--   Archimedean parameters $(u_R,a_R,u_C,k_C)$ for $K$ with `huR`, `huC` realising the archimedean components of $\mu$ are given. A splitting $E$ of the infinite ideles into the ideles is given, with `hE` requiring that $E(u)$ has infinite part $u$ and finite part $1$. A non-zero rational $a$ (`ha`) is given together with an infinite idele `aInf` whose underlying infinite adele is the image of $a$ (`haInf`), and an additive character `psiInf` of the infinite adeles with `hpsiInf` giving $\mathrm{psiInf}(x)=\psi_\infty(ax)$ for the standard archimedean character, while `hψinf` requires that the restriction of $\psi$ to the infinite component equals `psiInf`. Measures are given: $\nu_{\mathrm{add}}$ on the infinite adeles, required by `hν_add` to be $|a|^{1/2}$ times the pushforward of Lebesgue measure under the identification of the infinite adeles with the mixed space, and a Haar measure $\nu_{\mathrm{mul}}$ on the infinite ideles.
--
--   Finally `Warch` is a complex function on $\mathrm{GL}_3$ of the infinite adeles, and the hypothesis `hWarch` (summarised here) requires: `Warch` is non-zero and $K$-finite (its right translates by the orthogonal set `orth3` lie in a fixed finite-dimensional span); it is continuous and satisfies a rapid-decay bound in the archimedean root sizes, namely there is $t$ such that for every $N$ there is $C$ with $\|\mathrm{Warch}(g_\infty)\|\le C/((\prod_w r_1(w,g)r_2(w,g))^t(1+\mathrm{archRootSum}(g))^N)$; it is a `psiInf`-Whittaker function; it transforms under central scalars $z$ by $\omega(E z)$; for every admissible twist $\sigma$ of $\mathbb{Q}$ with real archimedean component given by $(t,e)$ and every $g_\infty$, there is an entire $P$ such that the archimedean zeta integral `archZeta30` of $h\mapsto\mathrm{Warch}(hg_\infty)$ against $\sigma\circ E$ converges in a half-plane and equals $P(s)$ times the archimedean factor of the Hecke datum of $K,\mu$ with parameters shifted by $t$ and $e$, with $P$ of exponential growth on vertical strips, with $|s_{\mathrm{im}}|^N$ times the product bounded on strips for every $N$, and with the dual integral `archZetaDual31` at $1-s$ equal to the product of the sign factors $\prod_{w\ \mathrm{real}}\varepsilon(a_R(w)+e)$, $\prod_{w\ \mathrm{complex}}i^{|k_C(w)|}$ and $\prod_w\lambda_\infty(w)$, times $\omega(E\,a_{\mathrm{Inf}})\sigma(E\,a_{\mathrm{Inf}})^3$, times $|a|^{3(s-1/2)}$, times $P(s)$ times the dual archimedean factor at $1-s$; and there exists an admissible twist $\sigma$ of $\mathbb{Q}$ and some $s$ with `archZeta30 ν_mul Warch (σ.comp E) s 1 ≠ 0`.
--
--   Under these hypotheses the conclusion asserts the following. First, the three archimedean clauses of `hWarch` are reproduced verbatim: `Warch` is non-zero, is $K$-finite, and is continuous with the stated rapid-decay majorant in the archimedean root sizes.
--
--   Second, there exists a floor $a_0:\{\text{primes}\}\to\mathbb{N}$ such that for every level function $a$ with $a_0(v)\le a(v)$ for all $v\in S$ there exist a family `Wloc` of local functions and a global function $W$ on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ with the following properties.
--
--   (i) `Wloc v = Wfin v` for every $v\notin S$.
--
--   (ii) For every $v\in S$: `Wloc v 1 = 1`; `Wloc v` is a $\psi_v$-Whittaker function; `Wloc v` is right invariant under some open subgroup of $\mathrm{GL}_3(\mathbb{Q}_v)$; there are $B$, $t$, $C$ such that `Wloc v h` vanishes unless both $\mathrm{detSize}(h)\mathrm{lastRowSup}(h)/\mathrm{minorSup}(h)^2\le B$ and $\mathrm{minorSup}(h)/\mathrm{lastRowSup}(h)^2\le B$, and in that range $\|\mathrm{Wloc}\,v\,h\|\le C$ divided by the $t$-th power of the product of these two quantities; and `Wloc v` transforms under central scalars $z$ by the local component of $\omega$ at $v$.
--
--   (iii) Factorisation: for every $g$ and every finite set $T\supseteq S$ of primes such that the component of $g$ at each $v\notin T$ lies in the maximal compact subgroup, $W(g)=\mathrm{Warch}(g_\infty)\prod_{v\in T}\mathrm{Wloc}\,v\,(g_v)$.
--
--   (iv) $W$ is continuous; (v) $W$ is a $\psi$-Whittaker function; (vi) $W(\mathrm{diag}(z,z,z)g)=\omega(z)W(g)$ for every idele $z$.
--
--   (vii) For every $v\in S$, $W$ is congruence-equivariant along $v$ at level $a(v)$ for the local component of $\omega$: for $k$ in `converseCongruenceSet3 v (a v)` and $u$ the $(2,2)$ entry of $k$, $W(g\cdot\iota_v(k))=\omega_v(u)W(g)$.
--
--   (viii) For every $v\in S$, the unipotent integral of $W$ along $v$ vanishes: the integral of $W(g\cdot\iota_v(u(0,x,0)))$ over $\{|x|_v\le q_v\}$ against the self-dual Haar measure at $v$ is zero for every $g$.
--
--   (ix) For every $p\notin S$, $W$ is right invariant under the image of the local maximal compact in the adelic group; and (x), (xi) $W$ is a Hecke eigenfunction for the images of the two generators $\mathrm{diag}(\varpi_p,1,1)$ and $\mathrm{diag}(\varpi_p,\varpi_p,1)$, with eigenvalues $\mathrm{N}p\cdot$`inducedE1 ℚ (inducedCoeff K μ) p` and $\mathrm{N}p\cdot$`inducedE2 ℚ (inducedCoeff K μ) p` respectively, in the sense that for every Hecke coset system of representatives the sum of the right translates equals the eigenvalue times $W$.
--
--   (xii) Finally, for every constant $c$ with $c$ times the adelic Haar volume of the adelic box equal to $1$: for every $g$ whose component at each $v\in S$ lies in `converseCongruenceSet3 v (a v)`, and every admissible twist $\chi$ of $\mathbb{Q}$ which is unramified at every $v\in S$, there exists a function $\mathcal{E}:\mathbb{C}\to\mathbb{C}$ which is entire, bounded on vertical strips, and for which there are $\sigma_1,\sigma_2$ with $\mathcal{E}(s)=\mathrm{globalZeta30}\,W\,\chi\,s\,g$ for $\mathrm{Re}(s)>\sigma_1$ and $\mathcal{E}(s)=c\cdot\mathrm{globalZetaDual31}\,W\,\chi\,(1-s)\,g$ for $\mathrm{Re}(s)<\sigma_2$.
--
--   This is the global assembly step of the cubic automorphic induction used in the Langlands–Tunnell argument: starting from a prescribed archimedean Whittaker vector together with the local data at the bad primes, it produces a global Whittaker function on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ with the Whittaker, central, Hecke-eigenvalue, congruence and vanishing-integral properties, and with global zeta integrals that continue to an entire function bounded on strips and satisfy the functional equation — precisely the input required by the $\mathrm{GL}_3$ converse theorem. It is used by [`LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad`](thm.html#LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_whittaker_zeta_fe_of_forall_not_mem_isInducedSphericalAt_of_arch.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda LanglandsTunnell.TateLocal MeasureTheory

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.exists_whittaker_zeta_fe_of_forall_not_mem_isInducedSphericalAt_of_arch
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hψS : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (Wfin : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (hfin : ∀ v, v ∉ S →
      IsGL3PsiWhittakerFn (psiLoc ψ v) (Wfin v) ∧
      IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) (Wfin v) ∧
      (Wfin v) 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (Wfin v))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : IsAdmissibleTwist ℚ ω ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S ↔ IsBadPlace K μ v)
    (hloc :
      ∀ v ∈ S, ∀ θ : ℂ, ‖θ‖ = 1 →
        ∃ (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → ℕ),
          (∀ i, IsLocallyConstant (ν i)) ∧
          (∀ i, 1 ≤ a i ∧ LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (ν i) (a i)) ∧
          (∑ i, (a i : ℤ)) =
            ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w ∧
          (∀ i, ‖((ν i (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) ∧
          ν 0 * ν 1 * ν 2 = localChar ω v ∧
          (∀ s : ℂ, (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i) s) =
            ((inducedEulerPoly ℚ (inducedCoeff K μ) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹) ∧
          (∏ i, LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ν i)) = θ ∧
          ∃ a₀ : ℕ, ∀ c : ℕ, a₀ ≤ c →
            ∃ W : LocalGL3 v → ℂ,
            W 1 = 1 ∧
            (IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v) W) ∧
            (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
          ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) ∧
            (∀ m : ℕ, (∑ i, a i) ≤ m → IsCongruenceEquivariantAt v m (localChar ω v) W) ∧
            (HasVanishingUnipotentIntegralAt v W) ∧
            (∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
              (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
              (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
                ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)) ∧
            (∀ (z : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v),
          W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((localChar ω v z : ℂˣ) : ℂ) * W g) ∧
              ∀ χ : (v.adicCompletion ℚ)ˣ →* ℂˣ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ 0 →
                ‖((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1 →
                ∀ g ∈ converseCongruenceSet3 v c,
                  (letI := localBorel ℚ v
      ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
        (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
          P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
        IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
          W χ g σ₀ ∧
        (∀ s : ℂ, σ₀ < s.re →
          localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
              W χ s g =
            (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i * χ) s) * P s) ∧
        IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
          (dualWhittakerFn3 W)
          χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
        ∃ a : Fin 3 → ℕ, (∀ i, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (ν i * χ) (a i)) ∧
          ∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
                W χ (1 - s) g =
              (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i * χ)⁻¹ (1 - s)) *
                ((∏ i, LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ν i * χ)) *
                  (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s))) * P s))
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
    M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
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
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (hWarch :
      Warch ≠ 0 ∧ IsKFinite Warch ∧
      (Continuous Warch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖Warch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) ∧
      IsGL3PsiWhittakerFn psiInf Warch ∧
      (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        Warch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω (E z) : ℂˣ) : ℂ) * Warch g) ∧
      (∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
        ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
        ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
          (∃ σ₀ : ℝ, IsArchZeta30ConvergentAbove ν_mul (fun h => Warch (h * gInf)) (σ.comp E) 1 σ₀ ∧
            ∀ s : ℂ, σ₀ < s.re →
              archZeta30 ν_mul (fun h => Warch (h * gInf)) (σ.comp E) s 1 =
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
          (∃ σ₁ : ℝ, IsArchZeta31ConvergentAbove ν_mul ν_add (dualWhittakerFn3 (fun h => Warch (h * gInf)))
              (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
            ∀ s : ℂ, σ₁ < (1 - s).re →
              archZetaDual31 ν_mul ν_add (fun h => Warch (h * gInf)) (σ.comp E) (1 - s) 1 =
                (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
                    fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
                  ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                      fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
                  ∏ w : InfinitePlace K, lambdaArch K w) *
                (((ω (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul Warch (σ.comp E) s 1 ≠ 0) :
      Warch ≠ 0 ∧ IsKFinite Warch ∧
      (Continuous Warch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖Warch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) ∧
      ∃ a₀ : HeightOneSpectrum (𝓞 ℚ) → ℕ, ∀ a : HeightOneSpectrum (𝓞 ℚ) → ℕ, (∀ v ∈ S, a₀ v ≤ a v) →
      ∃ (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ v, v ∉ S → Wloc v = Wfin v) ∧
      (∀ v ∈ S, Wloc v 1 = 1 ∧
        (IsGL3PsiWhittakerFn (psiLoc ψ v) (Wloc v)) ∧
        (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, (Wloc v) (g * k) = (Wloc v) g) ∧
        (∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
          (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → Wloc v h = 0) ∧
          (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
            ‖Wloc v h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)) ∧
        (∀ (z : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v),
      (Wloc v) (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((localChar ω v z : ℂˣ) : ℂ) * (Wloc v) g)) ∧
      (∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W g = Warch (archComponent3 (𝓞 ℚ) ℚ g) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v g)) ∧
      (Continuous W) ∧
      (IsGL3PsiWhittakerFn ψ W) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * W g) ∧
      (∀ v ∈ S, IsCongruenceEquivariantAlong v (a v) (localChar ω v) W) ∧
      (∀ v ∈ S, HasVanishingUnipotentIntegralAlong v W) ∧
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) W) ∧
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) W (cNormQ p * inducedE1 ℚ (inducedCoeff K μ) p)) ∧
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) W (cNormQ p * inducedE2 ℚ (inducedCoeff K μ) p)) ∧
      ∀ c : ℂ, c * ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ)).toReal : ℂ) = 1 →
        (∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ v ∈ S, componentAt3 (𝓞 ℚ) ℚ v g ∈ converseCongruenceSet3 v (a v)) →
      ∀ χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ χ → (∀ v ∈ S, IsUnramifiedCharAt χ v) →
        ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ LanglandsTunnell.LDatum.BoundedOnStrips E ∧ ∃ σ₁ σ₂ : ℝ,
          (∀ s : ℂ, σ₁ < s.re → E s = globalZeta30 W χ s g) ∧
          (∀ s : ℂ, s.re < σ₂ → E s = c * globalZetaDual31 W χ (1 - s) g)) := by sorry
