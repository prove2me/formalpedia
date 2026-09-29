-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_archWhittaker_torusPair_eq_gammaFactor_of_archWhittakerDatum
-- name    : LanglandsTunnell.RankinSelberg.exists_archWhittaker_torusPair_eq_gammaFactor_of_archWhittakerDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/974daf04-2057-5f23-aff9-cf22b0af2084
-- title:
--   Archimedean GL₂timesGL₃ torus-pair identity for the cubic induction
-- statement:
--   Setting. Let $K$ be a number field of degree $3$ over $\mathbb{Q}$, whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, and let $\mu\colon (\mathbb{A}_K)^\times\to\mathbb{C}^\times$ be a character of the ideles of $K$. The hypothesis `_hμ` asks that $\mu$ be an *admissible twist*: trivial on the principal ideles $K^\times$, continuous, and of absolute value $1$ everywhere. The hypothesis `_hns` asks that $\mu$ be *not of norm type*: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose restriction $p=\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ is unramified for $\eta$, one has $\mu(\varpi_{\mathfrak{P}})=\eta(\varpi_p)^{f(\mathfrak{P}/p)}$, where $\varpi$ denotes the idele with a uniformizer in the given place and $1$ elsewhere, and $f$ is the inertia degree; here 'unramified at $v$' means that the local component of the character is trivial on the units of the local integers.
--
--   Archimedean parameters of $\mu$. Data $uR,aR$ attached to the real places and $uC,kC$ attached to the complex places of $K$ are given, with $uR_w\in\mathbb{C}$, $aR_w\in\mathbb{Z}/2$, $uC_w\in\mathbb{C}$, $kC_w\in\mathbb{Z}$; the hypotheses `huR`, `huC` say that at each infinite place $w$ the archimedean local component of $\mu$ is $x\mapsto \|x\|^{m_w u_w}\,(x/\|x\|)^{a}$, with $m_w$ the multiplicity of $w$, the exponent $a$ being the representative $(aR_w)^{\mathrm{val}}\in\mathbb{Z}$ at a real place and $kC_w$ at a complex place.
--
--   The central character. A character $\omega$ of the ideles of $\mathbb{Q}$ is given, and `hω` has three conjuncts: $\omega$ is an admissible twist; at every prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ which is not a bad place for $(K,\mu)$, i.e. neither ramified in $K$ nor twist-ramified above in the sense of `IsTwistRamifiedAbove`, the character $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals $\mathrm{inducedE3}$ of the coefficient family $\mathfrak{P}\mapsto\mu(\varpi_{\mathfrak{P}})$ (zero at ramified $\mathfrak{P}$), that is, minus the coefficient of $X^3$ in the induced Euler polynomial at $p$; and, for every choice of archimedean parameter data satisfying the two conditions above, at each real place $v$ of $\mathbb{Q}$ the archimedean component of $\omega$ has exponent $\sum_{w\ \mathrm{real}}uR_w+\sum_{w\ \mathrm{complex}}2uC_w$ and integer part $\sum_{w\ \mathrm{real}}(aR_w)^{\mathrm{val}}+\sum_{w\ \mathrm{complex}}(kC_w+1)$ (finite sums over the infinite places of $K$).
--
--   Normalisations. A monoid section $E$ of the infinite ideles into the full ideles of $\mathbb{Q}$ is given, with `hE` saying that $E(u)$ has infinite part $u$ and trivial finite part. A rational number $a$ is given with $a\neq 0$ and, pinned by `ha1`, $a=-1$; $a_\infty$ is an infinite idele with underlying element the image of $a$, and $\psi_\infty$ is the additive character $x\mapsto \psi_{\mathrm{arch}}(a x)$ of the infinite adeles. Measures: $\nu_{\mathrm{add}}$ is $|a|^{1/2}$ times the transport of Lebesgue measure along the identification of the infinite adeles of $\mathbb{Q}$ with the mixed space, and $\nu_{\mathrm{mul}}$ is a Haar measure on the infinite ideles, the measurable structures being the Borel ones.
--
--   The abstract archimedean $\mathrm{GL}_2$ Whittaker datum. A real archimedean parameter $P$ is given: either $\mathrm{principal}\,(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb{C}$, $a_i\in\mathbb{Z}/2$, or $\mathrm{discrete}\,(u_0,n)$ with $n\geq 1$. The hypothesis `_hP₁` requires that if $P$ is principal then $|\operatorname{Re}(u_1-u_2)|<1$ (it is stated under an irrelevant quantification over the real places of $\mathbb{Q}$). Further given are a weight $kw_{\varepsilon,w}\in\mathbb{Z}$, a torus profile $Wr_{\varepsilon,w}\colon\mathbb{C}\to\mathbb{C}$, both indexed by a parity $\varepsilon\in\mathbb{Z}/2$ and an infinite place $w$ of $\mathbb{Q}$, and a function $WA_\varepsilon$ on $\mathrm{GL}_2(\mathbb{R})$, subject to the following laws, for every parity $\varepsilon$ and (where relevant) every real place $w$ of $\mathbb{Q}$.
--
--   Weight laws: `hkw1`, if $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $kw_{\varepsilon,w}=s(a_1+\varepsilon)+s(a_2+\varepsilon)$ in $\mathbb{C}$, where $s(b)$ is $0$ for $b=0$ and $1$ otherwise; `hkw2`, if $P=\mathrm{discrete}(u_0,n)$ then $kw_{\varepsilon,w}=n+1$.
--
--   Profile laws: `hWr1`, if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\varepsilon=a_1$ then $Wr_{\varepsilon,w}(-t)=(-1)^{a_1^{\mathrm{val}}}Wr_{\varepsilon,w}(t)$ for all real $t$; `hWr2`, if $P$ is discrete then $Wr_{\varepsilon,w}(t)=0$ for $t<0$; `hWr3`, if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\varepsilon=a_1+1$, there is $s_0$ such that for $\operatorname{Re}s>s_0$ the Mellin transform of $t\mapsto (Wr_{\varepsilon,w}(t)+(-1)^{a_1^{\mathrm{val}}}Wr_{\varepsilon,w}(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P$ twisted by $(0,a_1)$ at $s$; `hWr4`, for every $b\in\mathbb{Z}/2$ with $b=\varepsilon$ or $b=\varepsilon+\mathrm{sgn}(P)$, where $\mathrm{sgn}(P)$ is the central sign $a_1+a_2$, resp. $n+1 \bmod 2$, there is $s_0$ such that for $\operatorname{Re}s>s_0$ the Mellin transform of $t\mapsto (Wr_{\varepsilon,w}(t)+(-1)^{b^{\mathrm{val}}}Wr_{\varepsilon,w}(-t))/t$ converges and equals the archimedean factor of $P$ twisted by $(0,b)$ at $s$.
--
--   Laws of $WA$: `hWAN`, $WA_\varepsilon\big(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\,h\big)=\exp(-2\pi i a x)\,WA_\varepsilon(h)$; `hWAZ`, $WA_\varepsilon(z\cdot h)=|z|^{c(P)+1}(z/|z|)^{\mathrm{sgn}(P)^{\mathrm{val}}}WA_\varepsilon(h)$ for scalar matrices $z\in\mathbb{R}^\times$, where $c(P)$ is the central exponent $u_1+u_2$, resp. $2u_0$; `hWAK`, $WA_\varepsilon(h\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(kw_{\varepsilon,\mathrm{default}})(\kappa)\,WA_\varepsilon(h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt`, $WA_\varepsilon(\mathrm{diag}(t,1))=Wr_{\varepsilon,\mathrm{default}}(t)$ for $t\in\mathbb{R}^\times$; `hWAc`, $WA_\varepsilon$ is continuous. Finally $w_{0\mathbb{R}}\in\mathrm{GL}_2(\mathbb{R})$ is the antidiagonal permutation matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   Conclusion. There exists a function $W_{\mathrm{arch}}$ on $\mathrm{GL}_3$ of the infinite adeles of $\mathbb{Q}$ with the following properties.
--
--   (i) $W_{\mathrm{arch}}\neq 0$; it is $K$-finite in the sense of `IsKFinite`, i.e. there is a finite set $S$ of functions such that for every $k$ in `orth3` the right translate $x\mapsto W_{\mathrm{arch}}(xk)$ lies in the $\mathbb{C}$-span of $S$.
--
--   (ii) $W_{\mathrm{arch}}$ is continuous, and there is $t\in\mathbb{N}$ such that for every $N\in\mathbb{N}$ there is $C\in\mathbb{R}$ with
--   $$\|W_{\mathrm{arch}}(\mathrm{archComponent3}\,g)\|\le \frac{C}{\big(\prod_{w}\mathrm{archRoot}_1(w,g)\,\mathrm{archRoot}_2(w,g)\big)^{t}\,(1+\mathrm{archRootSum}(g))^{N}}$$
--   for all $g$ in the adelic $\mathrm{GL}_3$ of $\mathbb{Q}$, the product being over the infinite places of $\mathbb{Q}$ and $\mathrm{archRootSum}(g)=\sum_w(\mathrm{archRoot}_1(w,g)+\mathrm{archRoot}_2(w,g))$.
--
--   (iii) $W_{\mathrm{arch}}$ is a $\psi_\infty$-Whittaker function: $W_{\mathrm{arch}}(u(x,y,z)g)=\psi_\infty(x+y)\,W_{\mathrm{arch}}(g)$ for all $x,y,z$ and all $g$, with $u(x,y,z)$ the upper unipotent `upperUnipotent3`.
--
--   (iv) Central character: $W_{\mathrm{arch}}(z\cdot g)=\omega(E z)\,W_{\mathrm{arch}}(g)$ for every infinite idele $z$, viewed as a scalar matrix, and every $g$.
--
--   (v) Zeta package. For every admissible twist $\sigma$ of $\mathbb{Q}$, every $t\in\mathbb{C}$ and $e\in\mathbb{Z}$ such that $\sigma$ has archimedean component of exponent $t$ and integer part $e$ at each real place of $\mathbb{Q}$, and every $g_\infty\in\mathrm{GL}_3$ of the infinite adeles, there is an entire function $Q$ (bound to the name `P` in the statement, shadowing the archimedean parameter) such that, writing $W=h\mapsto W_{\mathrm{arch}}(h g_\infty)$, $\chi=\sigma\circ E$ and $D$ for the $L$-datum $\mathrm{heckeDatum}$ of $(K,\mu)$ with archimedean data $uR+t$, $aR+e \bmod 2$, $uC+t$, $kC$:
--   • there is $\sigma_0$ with `IsArchZeta30ConvergentAbove` for $(\nu_{\mathrm{mul}},W,\chi)$ at the identity above $\sigma_0$, i.e. the integrand $\alpha\mapsto W(\iota(\mathrm{diag}(\alpha,1))\,)\chi(\alpha)\|\alpha\|^{s-1}$ is $\nu_{\mathrm{mul}}$-integrable for $\operatorname{Re}s>\sigma_0$, and for such $s$
--   $$\mathrm{archZeta30}(\nu_{\mathrm{mul}},W,\chi,s,1)=Q(s)\cdot D.\mathrm{archFactor}(s),$$
--   where $D.\mathrm{archFactor}(s)=\prod\Gamma_{\mathbb{R}}(s+uR_w+t+s(aR_w+e))\cdot\prod\Gamma_{\mathbb{C}}(s+uC_w+t+|kC_w|/2)$ over the real, resp. complex, places of $K$;
--   • for all $\sigma_1,\sigma_2$ there are $C,A$ with $\|Q(s)\|\le C\exp(A|\operatorname{Im}s|)$ on the strip $\sigma_1\le\operatorname{Re}s\le\sigma_2$;
--   • for all $\sigma_1,\sigma_2$ and $N\in\mathbb{N}$ there are $C,T_0$ with $|\operatorname{Im}s|^{N}\,\|Q(s)\,D.\mathrm{archFactor}(s)\|\le C$ on that strip for $|\operatorname{Im}s|\ge T_0$;
--   • there is $\sigma_1$ with `IsArchZeta31ConvergentAbove` for $(\nu_{\mathrm{mul}},\nu_{\mathrm{add}})$, the dual Whittaker function $g\mapsto W(\mathrm{longWeyl3}\cdot{}^{t}g^{-1})$, the character $\chi^{-1}$ and the element $\mathrm{weylPrime3}\cdot{}^{t}1^{-1}$, above $\sigma_1$, and for all $s$ with $\sigma_1<\operatorname{Re}(1-s)$
--   $$\mathrm{archZetaDual31}(\nu_{\mathrm{mul}},\nu_{\mathrm{add}},W,\chi,1-s,1)=\Lambda\cdot\big(\omega(Ea_\infty)\,\sigma(Ea_\infty)^{3}\big)\cdot|a|^{3(s-1/2)}\cdot Q(s)\cdot D.\mathrm{archFactorDual}(1-s),$$
--   where $\Lambda=\prod_{w\ \mathrm{real}}\varepsilon(aR_w+e)\cdot\prod_{w\ \mathrm{complex}}i^{|kC_w|}\cdot\prod_{w}\lambda_{\mathrm{arch}}(w)$ over the places of $K$, with $\varepsilon(b)=1$ for $b=0$ and $i$ otherwise, and $\lambda_{\mathrm{arch}}(w)=1$ at real $w$ and $i$ at complex $w$, and $D.\mathrm{archFactorDual}$ is the dual archimedean factor, with $u$'s negated.
--
--   (vi) Non-vanishing: there exist an admissible twist $\sigma$ of $\mathbb{Q}$ and $s\in\mathbb{C}$ with $\mathrm{archZeta30}(\nu_{\mathrm{mul}},W_{\mathrm{arch}},\sigma\circ E,s,1)\neq 0$.
--
--   (vii) Torus-pair identity. There exist a parity $\mathrm{par}_0\in\mathbb{Z}/2$, an abscissa $\sigma_a\in\mathbb{R}$ and nonzero constants $e,\mathrm{ed}\in\mathbb{C}$ with
--   $$\mathrm{ed}=\Big(\mathrm{archRootNumber}\big(K,\ \text{the constant family }P,\ \text{the constant family }P^{\mathrm{bc}},\ uR,aR,uC,kC\big)\cdot(-1)^{\mathrm{sgn}(P)^{\mathrm{val}}}\cdot(-1)^{\#\{w\ \mathrm{complex}\}}\Big)\,e,$$
--   where $\mathrm{archRootNumber}$ is the product of the epsilon factors of the twisted parameters over the real and the complex places of $K$, and $P^{\mathrm{bc}}$ is the base change of $P$, such that, writing $\jmath(q)$ for the image of $q\in\mathrm{GL}_2(\mathbb{R})$ under the embedding at the default (real) place of $\mathbb{Q}$ into the adelic $\mathrm{GL}_2$, then into the adelic $\mathrm{GL}_3$, then taking the archimedean component:
--   • for every $k$ in the row-isometry subgroup of $\mathrm{GL}_2(\mathbb{R})$ (matrices of determinant of absolute value $1$ acting isometrically on rows) with $\det k=1$, and every $q\in\mathrm{GL}_2(\mathbb{R})$,
--   $$WA_{\mathrm{par}_0}(qk)\,W_{\mathrm{arch}}(\jmath(qk))=WA_{\mathrm{par}_0}(q)\,W_{\mathrm{arch}}(\jmath(q));$$
--   • for the same $k$ and $q$,
--   $$|\det(qk)|\,WA_{\mathrm{par}_0}\big(w_{0\mathbb{R}}\,{}^{t}(qk)^{-1}\big)\cdot \widetilde{W}_{\mathrm{arch}}(\jmath(qk))=|\det q|\,WA_{\mathrm{par}_0}\big(w_{0\mathbb{R}}\,{}^{t}q^{-1}\big)\cdot\widetilde{W}_{\mathrm{arch}}(\jmath(q)),$$
--   where $\widetilde{W}_{\mathrm{arch}}$ is the dual Whittaker function of $W_{\mathrm{arch}}$;
--   • for all $s$ with $\operatorname{Re}s>\sigma_a$, with $q=q(a_1,a_2)=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$,
--   $$\int_{0}^{\infty}\!\!\int_{\mathbb{R}} WA_{\mathrm{par}_0}(q)\,W_{\mathrm{arch}}(\jmath(q))\,|\det q|^{s-1/2}\,a_1^{-2}\,da_1\,da_2=e\cdot\Big(\prod\Gamma_{\mathbb{R}}(s+\tfrac12+x)\cdot\prod\Gamma_{\mathbb{C}}(s+\tfrac12+x)\Big),$$
--   the integrand being $0$ unless $a_1\neq0$ and $a_2>0$, and the two products being over the multisets $\mathrm{twistedGammaR}$ and $\mathrm{twistedGammaC}$ formed from the constant families $P$, $P^{\mathrm{bc}}$ twisted by $(uR,aR)$ at the real and $(uC,kC)$ at the complex places of $K$;
--   • for all $s$ with $\operatorname{Re}s>\sigma_a$, the same double integral with integrand $|\det q|\,WA_{\mathrm{par}_0}(w_{0\mathbb{R}}\,{}^{t}q^{-1})\,\widetilde{W}_{\mathrm{arch}}(\jmath(q))\,|\det q|^{s-1/2}a_1^{-2}$ equals $\mathrm{ed}$ times the corresponding product of $\Gamma_{\mathbb{R}}$- and $\Gamma_{\mathbb{C}}$-factors at $s+\tfrac12+x$ over the multisets built from the dual parameters $P^{\vee}$, $(P^{\mathrm{bc}})^{\vee}$ twisted by $(-uR,aR)$ and $(-uC,-kC)$.
--
--   This is the archimedean row of the Rankin–Selberg comparison underlying the cubic induction in the Langlands–Tunnell argument: it produces a $\mathrm{GL}_3$ archimedean Whittaker function whose zeta integrals and dual zeta integrals reproduce, up to an entire factor of moderate growth, the archimedean $L$- and $\varepsilon$-factors of the idele class character $\mu$ of the cubic field, and whose pairing against the abstract $\mathrm{GL}_2$ datum $(P,kw,Wr,WA)$ in Siegel coordinates is computed on both the standard and the dual side with the two constants linked by the archimedean root number. The hypotheses on the $\mathrm{GL}_2$ datum are stated abstractly, so no realisation of the datum as the archimedean part of an automorphic form is needed. It feeds the statement that the relevant $L$-function is entire and bounded on vertical strips, which is the input to the converse theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_archWhittaker_torusPair_eq_gammaFactor_of_archWhittakerDatum.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_archWhittaker_torusPair_eq_gammaFactor_of_archWhittakerDatum
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
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
    (a : ℚ) (ha : a ≠ 0) (ha1 : a = -1) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (P : RealArchParam)
    (_hP₁ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (kw : ZMod 2 → InfinitePlace ℚ → ℤ)
    (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
    (WA : ZMod 2 → GL (Fin 2) ℝ → ℂ)
    (hkw1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          (kw par w : ℂ) = signShift (a₁ + par) + signShift (a₂ + par))
    (hkw2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → kw par w = (n : ℤ) + 1)
    (hWr1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par ∨ b = par + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (hWAN : ∀ par : ZMod 2, ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
        WA par (unipotentGL2 x * h) = Complex.exp (-(2 * Real.pi * Complex.I * (a : ℂ) * x)) * WA par h)
    (hWAZ : ∀ par : ZMod 2, ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ),
        WA par (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h)
          = ((((|(z : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
              (((z : ℝ) : ℂ) / ((|(z : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) * WA par h)
    (hWAK : ∀ par : ZMod 2, ∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
        WA par (h * κ) = (archWeightCharℝ (kw par default) ⟨κ, hκ⟩ : ℂ) * WA par h)
    (hWAt : ∀ par : ZMod 2, ∀ t : ℝˣ, WA par (diagOne t) = Wr par default (t : ℝ))
    (hWAc : ∀ par : ZMod 2, Continuous (WA par))
    (w₀R : GL (Fin 2) ℝ) (hw₀R : (w₀R : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0]) :
    ∃ Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ,
      (Warch ≠ 0 ∧ IsKFinite Warch ∧
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
        ∃ s : ℂ, archZeta30 ν_mul Warch (σ.comp E) s 1 ≠ 0) ∧
      ∃ (par₀ : ZMod 2) (σa : ℝ) (e ed : ℂ), e ≠ 0 ∧ ed ≠ 0 ∧
        ed = (archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val * (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card) * e ∧
        (∀ k ∈ AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 → ∀ q : GL (Fin 2) ℝ,
            WA par₀ (q * k) * Warch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (q * k))))
              = WA par₀ q * Warch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) ∧
        (∀ k ∈ AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 → ∀ q : GL (Fin 2) ℝ,
            ((((|(Matrix.GeneralLinearGroup.det (q * k) : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv (q * k))) *
                dualWhittakerFn3 Warch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (q * k)))))
              = ((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) *
                dualWhittakerFn3 Warch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q))))) ∧
        (∀ s : ℂ, σa < s.re →
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                ((WA par₀ q * Warch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = e * (((twistedGammaR K (archOfParamR K P) uR aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod)) ∧
        (∀ s : ℂ, σa < s.re →
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 Warch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = ed * (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
                    (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod)) := by sorry
