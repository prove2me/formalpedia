-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad
-- name    : LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/4794504d-0e7b-54d3-9d93-5211d1f7de38
-- title:
--   Existence of a cubic-induction datum: archimedean and bad-place package
-- statement:
--   **Setting.** $K$ is a number field whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, subject to `_hdeg` : $[K:\mathbb{Q}]=3$. Further data: an additive character $\psi$ of the adele ring of $\mathbb{Q}$ with `_h\psi` : `IsGlobalAddChar`, i.e. $\psi$ is trivial on the image of $\mathbb{Q}$, continuous and non-trivial; a character $\mu \colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ with `_h\mu` : `IsAdmissibleTwist`, i.e. $\mu$ is trivial on principal ideles, continuous and of absolute value $1$ everywhere.
--
--   **Level hypotheses.** `_hlev` requires $\operatorname{addCharLevel}(\psi_v)=0$ — the supremum of the $n \in \mathbb{Z}$ with $\psi_v$ trivial on $\{x : v(x) \le \exp n\}$ is $0$, where $\psi_v =$ `psiLoc` $\psi\, v$ is $\psi$ composed with the inclusion of the $v$-adic completion into the adeles — at every finite place $v$ of $\mathbb{Q}$ which is *not* bad for $(K,\mu)$, a place $v$ being bad when either some prime of $K$ above $v$ has ramification index $\ne 1$ (`IsRamifiedIn`) or the predicate `IsTwistRamifiedAbove K μ v` holds. The hypothesis `hlev` requires the same vanishing of the level at *every* finite place of $\mathbb{Q}$, and hence implies `_hlev`.
--
--   **Non-norm-type hypothesis.** `_hns` asserts that there is no admissible twist $\eta$ of $\mathbb{Q}$ (trivial on principal ideles, continuous, unitary) such that for every prime $\mathfrak{P}$ of $K$ at which $\mu$ is unramified and whose trace $\mathfrak{p} = \mathfrak{P} \cap \mathcal{O}_{\mathbb{Q}}$ is unramified for $\eta$ one has $\mu(\varpi_{\mathfrak{P}}) = \eta(\varpi_{\mathfrak{p}})^{f(\mathfrak{P}/\mathfrak{p})}$, where $\varpi$ denotes the idele `uniformizerIdele` at the place in question and $f$ is `inertiaDeg'`.
--
--   **Archimedean parameters of $\mu$.** Functions $uR, aR$ on the real places of $K$ (values in $\mathbb{C}$ and in $\mathbb{Z}/2$) and $uC, kC$ on the complex places (values in $\mathbb{C}$ and in $\mathbb{Z}$), together with `huR` and `huC`, which state `IsArchCompAt K μ w` at each infinite place $w$: the local component of $\mu$ at $w$ is $x \mapsto \|x\|^{\,\mathrm{mult}(w)\,u}\,(x/\|x\|)^{a}$, with $(u,a) = (uR\,w, (aR\,w).\mathrm{val})$ at a real place and $(u,a) = (uC\,w, kC\,w)$ at a complex place.
--
--   **The central character $\omega$.** A character $\omega \colon (\mathbb{A}_{\mathbb{Q}})^\times \to \mathbb{C}^\times$ subject to the three clauses of `hω`: (1) $\omega$ is an admissible twist of $\mathbb{Q}$; (2) at every finite place $p$ which is not bad for $(K,\mu)$, $\omega$ is unramified and $\operatorname{eulerCoeff}_{\mathbb{Q}}(\omega,p) = \omega(\varpi_p)$ equals `inducedE3` $\mathbb{Q}\,(\text{inducedCoeff } K\,\mu)\,p$, i.e. minus the coefficient of $X^3$ in the induced Euler polynomial at $p$ formed from the coefficients $\mathfrak{P} \mapsto \mu(\varpi_{\mathfrak{P}})$ (set to $0$ at primes where $\mu$ ramifies); (3) for every quadruple $(uR,aR,uC,kC)$ of archimedean parameters satisfying the two `IsArchCompAt` conditions for $\mu$ as above, and every real place $v$ of $\mathbb{Q}$, `IsArchCompAt ℚ ω v` holds with exponents
--   $$u = \sum_{w \text{ real}} uR\,w + \sum_{w \text{ complex}} 2\,uC\,w, \qquad a = \sum_{w \text{ real}} (aR\,w).\mathrm{val} + \sum_{w \text{ complex}} (kC\,w + 1),$$
--   the sums being taken over the infinite places of $K$ (as finite sums `∑ᶠ`).
--
--   **Splitting of the infinite ideles.** A monoid homomorphism $E$ from the units of the infinite adele ring of $\mathbb{Q}$ to the idele group, with `hE` : $\operatorname{infPart}(E\,u) = u$ and $\operatorname{finPart}(E\,u) = 1$ for all $u$.
--
--   **Normalisation at infinity.** A non-zero rational $a$ (hypothesis `ha`), a unit $a_\infty$ of the infinite adele ring whose underlying element is the image of $a$ (`haInf`), the additive character $\psi_\infty$ of the infinite adele ring given by $\psi_\infty(x) = \mathrm{psiArch}(a\,x)$ (`hpsiInf`), and `hψinf` : the precomposition of $\psi$ with the inclusion of the infinite adeles into the adeles equals $\psi_\infty$. Measures: $\nu_{\mathrm{add}}$ on the infinite adele ring equal (by `hν_add`) to $|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the ring equivalence `InfiniteAdeleRing.ringEquiv_mixedSpace ℚ`, and a Haar measure $\nu_{\mathrm{mul}}$ on the units of the infinite adele ring; the two spaces carry Borel measurable structures.
--
--   **The archimedean Whittaker function.** A function $W_\infty$ on $\mathrm{GL}_3$ of the infinite adele ring, subject to the seven clauses of `hWarch`:
--
--   1. $W_\infty \ne 0$;
--
--   2. `IsKFinite W_∞`: the right translates of $W_\infty$ by elements of `orth3` all lie in the span of one finite set of functions;
--
--   3. $W_\infty$ is continuous, and there is $t \in \mathbb{N}$ such that for every $N \in \mathbb{N}$ there is $C$ with $\|W_\infty(g_\infty)\| \le C / \bigl((\prod_{w} \mathrm{archRoot}_1(w,g)\,\mathrm{archRoot}_2(w,g))^t (1 + \mathrm{archRootSum}(g))^N\bigr)$ for all adelic $g \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, $g_\infty$ its archimedean component;
--
--   4. `IsGL3PsiWhittakerFn ψ_∞ W_∞`: $W_\infty(u(x,y,z)g) = \psi_\infty(x+y)\,W_\infty(g)$ for upper unipotent $u(x,y,z)$;
--
--   5. $W_\infty(\mathrm{scalar}(z)\,g) = \omega(E\,z)\,W_\infty(g)$ for all units $z$ of the infinite adele ring;
--
--   6. the zeta clause: for every admissible twist $\sigma$ of $\mathbb{Q}$, every $t \in \mathbb{C}$ and $e \in \mathbb{Z}$ with `IsArchCompAt ℚ σ v t e` at every real place $v$ of $\mathbb{Q}$, and every $g_\infty \in \mathrm{GL}_3$ of the infinite adele ring, there is an entire function $P$ on $\mathbb{C}$ such that, writing $W = (h \mapsto W_\infty(h\,g_\infty))$ and $L$ for the archimedean factor `archFactor` of the $L$-datum `heckeDatum K μ` with parameters $(uR + t,\ aR + e \bmod 2,\ uC + t,\ kC)$ (a product of $\Gamma_{\mathbb{R}}$-factors over the real places of $K$ and $\Gamma_{\mathbb{C}}$-factors over the complex places, shifted by $uR\,w + t + \mathrm{signShift}(aR\,w + e)$ and $uC\,w + t + |kC\,w|/2$ respectively): (a) there is $\sigma_0$ with `IsArchZeta30ConvergentAbove` for $\nu_{\mathrm{mul}}$, $W$, $\sigma \circ E$ at the identity above $\sigma_0$, and for $\operatorname{Re} s > \sigma_0$ the zeta integral $\mathrm{archZeta30}(\nu_{\mathrm{mul}}, W, \sigma \circ E, s, 1) = P(s)\,L(s)$; (b) on every vertical strip $\sigma_1 \le \operatorname{Re} s \le \sigma_2$ there are $C, A$ with $\|P(s)\| \le C \exp(A|\operatorname{Im} s|)$; (c) on every vertical strip and for every $N \in \mathbb{N}$ there are $C, T_0$ with $|\operatorname{Im} s|^N \|P(s) L(s)\| \le C$ once $|\operatorname{Im} s| \ge T_0$; (d) there is $\sigma_1$ with `IsArchZeta31ConvergentAbove` for $\nu_{\mathrm{mul}}, \nu_{\mathrm{add}}$, the function $\mathrm{dualWhittakerFn3}\,W$, the character $(\sigma \circ E)^{-1}$ and the point $w' \cdot {}^{t}1^{-1}$ above $\sigma_1$, and for $\operatorname{Re}(1-s) > \sigma_1$ the functional equation
--   $$\mathrm{archZetaDual31}(\nu_{\mathrm{mul}},\nu_{\mathrm{add}}, W, \sigma \circ E, 1-s, 1) = \varepsilon \cdot \bigl(\omega(E\,a_\infty)\,\sigma(E\,a_\infty)^3\bigr)\, |a|^{3(s-1/2)}\, P(s)\, L^{\vee}(1-s),$$
--   where $L^{\vee}$ is `archFactorDual` of the same $L$-datum (the same $\Gamma$-factors with the $u$-shifts negated) and $\varepsilon = \prod_{w \text{ real}} \mathrm{signEpsilon}(aR\,w + e) \cdot \prod_{w \text{ complex}} i^{|kC\,w|} \cdot \prod_{w} \mathrm{lambdaArch}\,K\,w$, the products being over the infinite places of $K$, with $\mathrm{signEpsilon}(0)=1$, $\mathrm{signEpsilon}(1)=i$ and $\mathrm{lambdaArch}$ equal to $1$ at real and to $i$ at complex places;
--
--   7. there are an admissible twist $\sigma$ of $\mathbb{Q}$ and a point $s$ with $\mathrm{archZeta30}(\nu_{\mathrm{mul}}, W_\infty, \sigma \circ E, s, 1) \ne 0$.
--
--   **Conclusion.** For every set $D$ of adelic $\mathrm{GL}_2$-points, every family $U$ of subgroups of adelic $\mathrm{GL}_2$ indexed by ideals of $\mathcal{O}_{\mathbb{Q}}$, and every family $\mathrm{gen}$ of adelic $\mathrm{GL}_2$-points indexed by the finite places, there exist a finite set $S$ of finite places of $\mathbb{Q}$ whose underlying set is exactly $\{v : v \text{ bad for } (K,\mu)\}$, and a `CubicInductionData` $X_0$ — consisting of a form $X_0.\mathrm{form}$, a Whittaker function $X_0.\mathrm{whittaker}$, local Whittaker functions $X_0.\mathrm{whittakerLoc}\,v$ on $\mathrm{GL}_3$ of the $v$-adic completion, an archimedean Whittaker function $X_0.\mathrm{whittakerArch}$, a central character $X_0.\mathrm{centralChar}$ and a dual Whittaker function $X_0.\mathrm{dualWhittaker}$ — with all of the following properties, the carrier pins being `productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)` (Borel structure and adelic Haar measure on adelic $\mathrm{GL}_2$, the set $D$, full central subgroup, the level family $U$, the generators $\mathrm{gen}$, and the adelic additive Haar measure conditioned on the adelic box):
--
--   1. `IsCubicInductionDataOn K pins ψ μ S X₀` holds, that is: $X_0.\mathrm{form}$ is left invariant under the rational points of $\mathrm{GL}_3$; it transforms under central adelic scalars by $X_0.\mathrm{centralChar}$, which is trivial on principal ideles; it is cuspidal along both maximal parabolic subgroups $P_{21}$ and $P_{12}$ relative to the pins; $X_0.\mathrm{whittaker}$ is the $\psi$-Whittaker coefficient `whittaker3` of $X_0.\mathrm{form}$, satisfies the $\psi$-Whittaker law $W(u(x,y,z)g) = \psi(x+y)W(g)$, and its translates by the mirabolic index set sum (as a `HasSum`) to $X_0.\mathrm{form}$; each $X_0.\mathrm{whittakerLoc}\,v$ satisfies the $\psi_v$-Whittaker law; for every finite set $T$ containing $S$ and every $g$ whose components outside $T$ lie in the local maximal compact subgroups, $X_0.\mathrm{whittaker}(g)$ factorises as $X_0.\mathrm{whittakerArch}$ of the archimedean component times the product over $v \in T$ of $X_0.\mathrm{whittakerLoc}\,v$ of the component at $v$; for $v \notin S$ the local function is induced-spherical at $v$ with coefficients `inducedCoeff K μ` relative to the maximal compact subgroup, and if moreover $v$ is unramified in $K$ it is right invariant under the congruence set `congruenceK1` at level `inducedLevelAt K μ v` $= \sum_{\mathfrak{P} \mid v} f(\mathfrak{P}/v)\,a(\mu_{\mathfrak{P}})$; every $X_0.\mathrm{whittakerLoc}\,v$ has the multiplicity-one property for $\psi_v$; $X_0.\mathrm{form}$ is of moderate growth and has iota moments; $X_0.\mathrm{whittakerArch}$ is $K$-finite; $X_0.\mathrm{whittaker}$ has the half-plane property; and the dual clauses: $X_0.\mathrm{dualWhittaker}$ is the $\psi^{-1}$-Whittaker coefficient of the dual form of $X_0.\mathrm{form}$, satisfies the $\psi^{-1}$-Whittaker law, its mirabolic translates sum to the dual form, the dual form has iota moments and $X_0.\mathrm{dualWhittaker}$ has the half-plane property.
--
--   2. $X_0.\mathrm{form}$, $X_0.\mathrm{whittaker}$ and $X_0.\mathrm{dualWhittaker}$ are continuous.
--
--   3. $X_0.\mathrm{whittaker}$ and $X_0.\mathrm{dualWhittaker}$ are gauge-majorised (`IsGaugeMajorised3`): each vanishes off a root-level region and satisfies there the rapid-decay bounds in the archimedean root sizes.
--
--   4. $X_0.\mathrm{whittakerArch} \ne 0$.
--
--   5. $X_0.\mathrm{whittakerLoc}\,v\,(1) = 1$ for every $v \in S$.
--
--   6. For $v \in S$, every non-zero element $G$ of the cyclic subspace generated by the right translates of $X_0.\mathrm{whittakerLoc}\,v$ regenerates it: $X_0.\mathrm{whittakerLoc}\,v$ lies in the cyclic subspace of $G$.
--
--   7. For $v \in S$ there is an open subgroup $U_v$ of $\mathrm{GL}_3$ of the $v$-adic completion under which $X_0.\mathrm{whittakerLoc}\,v$ is right invariant.
--
--   8. For $v \notin S$, $X_0.\mathrm{whittakerLoc}\,v\,(1) = 1$ and `HasSphericalTorusValuesAt (inducedCoeff K μ) v` holds for it: its values at the torus points $\mathrm{iotaTorusLocal}\,v\,n$ and at the two-row points $\mathrm{twoRowPointLocal}\,v\,k_1\,(k_2+1)$ with $k_2 + 1 \le k_1$ are the prescribed normalised combinations of the spherical torus values in the induced coefficients $e_1, e_2, e_3$ at $v$.
--
--   9. For $v \in S$ which is unramified in $K$, there is a non-zero $W$ in the cyclic subspace of $X_0.\mathrm{whittakerLoc}\,v$ which is right invariant under `congruenceK1` at level `inducedLevelAt K μ v`, and which, provided $\operatorname{addCharLevel}(\psi_v)=0$, satisfies $W(1)=1$ and `HasSphericalTorusValuesAt (inducedCoeff K μ) v W`.
--
--   10. $X_0.\mathrm{whittakerArch} = W_\infty$ and $X_0.\mathrm{centralChar} = \omega$.
--
--   11. Admissibility at the bad places: for $v \in S$ and every open subgroup $U_v$ there is a finite set $B$ of functions such that every $U_v$-right-invariant element of the cyclic subspace of $X_0.\mathrm{whittakerLoc}\,v$ lies in the $\mathbb{C}$-span of $B$.
--
--   12. For $v \in S$ the local component $\omega_v$ of $\omega$ has absolute value $1$ on all local units, and $X_0.\mathrm{whittakerLoc}\,v(\mathrm{scalar}(t)h) = \omega_v(t)\,X_0.\mathrm{whittakerLoc}\,v(h)$.
--
--   13. For $v \in S$ ramified in $K$ there are natural numbers $e$ and $N$ such that: $\omega_v$ has conductor exponent $e$ (trivial on the higher unit group of level $e$, and for each $m < e$ non-trivial on some unit of level $m$); for every $M \in \mathbb{N}$ such that each prime $w$ of $K$ above $v$ admits a conductor exponent $a_w \le M$ for $\mu_w$, one has
--   $$N \le 2\Bigl(\sum_{w \mid v} f_w\bigl(e_w\,(2(48+e+M) + n_w + 2) + M + n_w + 1\bigr) + (48+e+M)\Bigr),$$
--   where $f_w$ is `inertiaDeg'`, $e_w$ is `ramificationIdx'` and $n_w = \operatorname{addCharLevel}$ of the standard local additive character of $K$ at $w$; and $X_0.\mathrm{whittakerLoc}\,v$ is right invariant under every $k$ in the local maximal compact subgroup all of whose entries satisfy $v(k_{ij} - \delta_{ij}) \le \exp(-N)$, i.e. under the principal congruence subgroup of level $N$.
--
--   This is the core construction step for the automorphic induction of an idele class character $\mu$ of a non-Galois cubic field $K$ to a cusp form on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$: from a prescribed archimedean Whittaker function whose twisted $\mathrm{GL}_3 \times \mathrm{GL}_1$ zeta integrals are entire multiples of the archimedean factors of the Hecke $L$-datum of $\mu$ with the expected functional equation, it produces a global cubic-induction datum with induced spherical local data outside the bad places and an explicit level and central-character package at the bad ones. It is used by `hasCubicInductionForm_arch_torusValues_localPackage_bad`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda
  MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (_hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
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
    ∀ (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
      (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ),
      ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)), (S : Set (HeightOneSpectrum (𝓞 ℚ))) = {v | IsBadPlace K μ v} ∧
      ∃ X₀ : CubicInductionData,
        IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
          (S : Set (HeightOneSpectrum (𝓞 ℚ))) X₀ ∧
        Continuous X₀.form ∧ Continuous X₀.whittaker ∧ Continuous X₀.dualWhittaker ∧
        IsGaugeMajorised3 ℚ X₀.whittaker ∧ IsGaugeMajorised3 ℚ X₀.dualWhittaker ∧
        X₀.whittakerArch ≠ 0 ∧
        (∀ v ∈ S, X₀.whittakerLoc v 1 = 1) ∧
        (∀ v ∈ S, ∀ G ∈ gl3CyclicSubspace (X₀.whittakerLoc v), G ≠ 0 →
          X₀.whittakerLoc v ∈ gl3CyclicSubspace G) ∧
        (∀ v ∈ S, ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
          ∀ k ∈ Uv, ∀ g : LocalGL3 v, X₀.whittakerLoc v (g * k) = X₀.whittakerLoc v g) ∧
        (∀ v, v ∉ S → X₀.whittakerLoc v 1 = 1 ∧
          HasSphericalTorusValuesAt (inducedCoeff K μ) v (X₀.whittakerLoc v)) ∧
        (∀ v ∈ S, ¬ IsRamifiedIn K v → ∃ W ∈ gl3CyclicSubspace (X₀.whittakerLoc v), W ≠ 0 ∧
          (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, W (g * k) = W g) ∧
          (LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
            W 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v W)) ∧
        X₀.whittakerArch = Warch ∧

        X₀.centralChar = ω ∧
        (∀ v ∈ S, ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
            ∃ B : Finset (LocalGL3 v → ℂ), ∀ G ∈ gl3CyclicSubspace (X₀.whittakerLoc v),
              (∀ k ∈ Uv, ∀ g : LocalGL3 v, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) ∧
        (∀ v ∈ S,
          (∀ z : (v.adicCompletion ℚ)ˣ, ‖((localChar ω v z : ℂˣ) : ℂ)‖ = 1) ∧
          ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
            X₀.whittakerLoc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
              ((localChar ω v t : ℂˣ) : ℂ) * X₀.whittakerLoc v h) ∧
        (∀ v ∈ S, IsRamifiedIn K v →
          ∃ (e N : ℕ), LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar ω v) e ∧
            (∀ M : ℕ, (∀ w ∈ primeFibre ℚ K v, ∃ aw : ℕ, aw ≤ M ∧
                LanglandsTunnell.TateLocal.HasConductorExponentAt K w (localChar μ w) aw) →
              (N : ℤ) ≤ 2 * ((∑ᶠ w ∈ primeFibre ℚ K v,
                  ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal : ℤ) *
                    ((Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal : ℤ) *
                        (2 * ((48 : ℤ) + e + M) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 2) +
                      M + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1)) +
                ((48 : ℤ) + e + M))) ∧
            ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
              (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
                  (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(N : ℤ))) →
              ∀ g : LocalGL3 v, X₀.whittakerLoc v (g * k) = X₀.whittakerLoc v g) := by sorry
