-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/850ac074-6629-5e90-86a4-a9e36c17f155
-- title:
--   Weight-one torus-pair identities for the conjugate-block Gaussian section
-- statement:
--   Throughout, $K$ is a number field carrying an integral $\mathcal O_{\mathbb Q}$-algebra structure on $\mathcal O_K$, and $\mu$ is a character of the idele units of $K$ with values in $\mathbb C^{\times}$.
--
--   **The cubic datum and the character $\mu$.** The hypothesis `_hdeg` states $[K:\mathbb Q]=3$. The hypothesis `_hμ` is `IsAdmissibleTwist K μ`: $\mu$ is trivial on the principal ideles coming from $K^{\times}$, continuous, and of absolute value $1$ on all ideles. The hypothesis `_hns` excludes descent to $\mathbb Q$: there is no admissible twist $\eta$ of $\mathbb Q$ such that for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified (its local character is trivial on the local units) and such that $\eta$ is unramified at the prime $\mathfrak p$ of $\mathcal O_{\mathbb Q}$ below $\mathfrak P$, one has $\mu(\varpi_{\mathfrak P}) = \eta(\varpi_{\mathfrak p})^{f}$, where $\varpi$ denotes the uniformizer idele and $f$ is the inertia degree of $\mathfrak P$ over $\mathfrak p$.
--
--   **Archimedean shape of $\mu$.** Functions $u_R, a_R$ on the real places and $u_C, k_C$ on the complex places of $K$ are given, with values in $\mathbb C$, $\mathbb Z/2$, $\mathbb C$, $\mathbb Z$ respectively. The hypotheses `huR` and `huC` assert `IsArchCompAt` at each infinite place: for every real $w$ and every $x \in (K_w)^{\times}$, the local archimedean component of $\mu$ at $w$ equals $\|x\|^{\mathrm{mult}(w)\,u_R(w)}\,(x/\|x\|)^{a_R(w).\mathrm{val}}$, and similarly at each complex $w$ with exponents $u_C(w)$ and $k_C(w)$.
--
--   **The induced character $\omega$ of $\mathbb Q$.** A character $\omega$ of the ideles of $\mathbb Q$ is given, and `hω` is a threefold conjunction: $\omega$ is an admissible twist of $\mathbb Q$; for every prime $p$ of $\mathcal O_{\mathbb Q}$ which is not a bad place for $(K,\mu)$ — that is, $p$ is neither ramified in $K$ nor twist-ramified above — $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals `inducedE3 ℚ (inducedCoeff K μ) p`, the negative of the degree-$3$ coefficient of the induced Euler polynomial formed from the coefficients $\mathfrak P \mapsto \mu(\varpi_{\mathfrak P})$ (set to $0$ at ramified $\mathfrak P$); and, for *any* data $u_R,a_R,u_C,k_C$ satisfying the same `IsArchCompAt` conditions as above (the quantifiers here shadow the ambient ones), the archimedean component of $\omega$ at every real place $v$ of $\mathbb Q$ has exponent $\sum_{w\text{ real}} u_R(w) + \sum_{w\text{ complex}} 2u_C(w)$ and integer parameter $\sum_{w\text{ real}} a_R(w).\mathrm{val} + \sum_{w\text{ complex}} (k_C(w)+1)$ (finite sums over infinite places).
--
--   **Adelic normalisations.** A monoid homomorphism $E$ from the infinite idele units to the idele units of $\mathbb Q$ is given with `hE`: the infinite part of $E(u)$ is $u$ and its finite part is $1$. A rational number $a$ is given with $a \neq 0$ and $a=-1$, together with an infinite idele unit $a_{\infty}$ whose underlying element is the image of $a$, and an additive character $\psi_{\infty}$ of the infinite adeles with $\psi_{\infty}(x) = \psi_{\mathrm{arch}}(a\,x)$ for the standard archimedean character $\psi_{\mathrm{arch}}$. Measurable and Borel structures on the infinite adeles and their units are assumed; $\nu_{\mathrm{add}}$ is the measure $|a|^{1/2}$ times the push-forward of Lebesgue measure under the inverse of the mixed-space ring equivalence, and $\nu_{\mathrm{mul}}$ is a Haar measure on the infinite idele units.
--
--   **The $GL_2$ parameter and its Whittaker data.** $P$ is a real archimedean parameter (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u,k)$ with $k\ge 1$), subject to `_hP₁`: in the principal case $|\mathrm{Re}(u_1-u_2)|<1$. Data $k_w(\varepsilon, v) \in \mathbb Z$, $W_r(\varepsilon, v, \cdot): \mathbb R \to \mathbb C$ and $W_A(\varepsilon, \cdot): GL_2(\mathbb R) \to \mathbb C$ are given, indexed by a parity $\varepsilon \in \mathbb Z/2$ and (for the first two) by an infinite place $v$ of $\mathbb Q$. The hypotheses on them are: `hkw1`, in the principal case $k_w(\varepsilon,v) = \mathrm{signShift}(a_1+\varepsilon) + \mathrm{signShift}(a_2+\varepsilon)$ as complex numbers, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$; `hkw2`, in the discrete case with lowest weight $n$, $k_w(\varepsilon,v) = n+1$; `hWr1`, in the principal case with $a_1=a_2$ and $\varepsilon=a_1$, the parity law $W_r(\varepsilon,v,-t) = (-1)^{a_1.\mathrm{val}}W_r(\varepsilon,v,t)$; `hWr2`, in the discrete case $W_r(\varepsilon,v,t)=0$ for $t<0$; `hWr3`, in the principal case with $a_1=a_2$ and $\varepsilon = a_1+1$, existence of an abscissa beyond which the Mellin transform of $t \mapsto (W_r(\varepsilon,v,t)+(-1)^{a_1.\mathrm{val}}W_r(\varepsilon,v,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P$ twisted by $(0,a_1)$; `hWr4`, for $b = \varepsilon$ or $b = \varepsilon + P.\mathrm{centralSign}$, existence of an abscissa beyond which the Mellin transform of $t \mapsto (W_r(\varepsilon,v,t)+(-1)^{b.\mathrm{val}}W_r(\varepsilon,v,-t))/t$ converges and equals the archimedean factor of $P$ twisted by $(0,b)$. For $W_A$: `hWAN`, $W_A(\varepsilon, n(x)h) = e^{-2\pi i a x}W_A(\varepsilon,h)$ for the unipotent $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; `hWAZ`, $W_A(\varepsilon, zI\cdot h) = |z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}W_A(\varepsilon,h)$; `hWAK`, $W_A(\varepsilon, h\kappa) = \mathrm{archWeightChar}_{\mathbb R}(k_w(\varepsilon,\mathrm{default}))(\kappa)\,W_A(\varepsilon,h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt`, $W_A(\varepsilon,\mathrm{diag}(t,1)) = W_r(\varepsilon,\mathrm{default},t)$ for $t \in \mathbb R^{\times}$; and `hWAc`, continuity of each $W_A(\varepsilon,\cdot)$. Finally $w_{0R} \in GL_2(\mathbb R)$ has matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   **The Levi datum.** A real place $w_0$ of $K$ is fixed, and a second real archimedean parameter $P_2$ subject to `hP₂`: either there are two further real places $w_1,w_2$ of $K$, pairwise distinct from $w_0$ and exhausting the infinite places, with $P_2 = \mathrm{principal}(u_R(w_1),a_R(w_1),u_R(w_2),a_R(w_2))$; or there is a complex place $w_C$ such that $w_C,w_0$ exhaust the infinite places and either $k_C(w_C)\neq 0$ and $P_2 = \mathrm{discrete}(u_C(w_C),|k_C(w_C)|)$, or $k_C(w_C)=0$ and $P_2 = \mathrm{principal}(u_C(w_C),0,u_C(w_C),1)$. An archimedean Whittaker datum $D$ of type $P_2$ is given (a function $W_D$ on $M_2(\mathbb R)$ with the unipotent and central transformation laws, smoothness, growth and Tate-type zeta bundle recorded in `ArchDatumR`), together with $k_0 \in \mathbb Z$, and: `hDW`, $W_D(x r) = \mathrm{archWeightChar}_{\mathbb R}(k_0)(r)W_D(x)$ for $r$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, $W_D$ is a Casimir eigenfunction, $\mathrm{matrixCasimir}\,W_D(x) = P_2.\mathrm{laplaceEigenvalue}\cdot W_D(x)$ for all $x$ with $\det x \neq 0$; `hDnz`, $W_D$ does not vanish identically on $GL_2(\mathbb R)$; `hk₀min`, in the principal case $k_0 \in \{0,1\}$ and $k_0 \equiv a_1+a_2 \bmod 2$, in the discrete case with lowest weight $m$ one has $k_0 = m+1$.
--
--   **Weight-one branch and the section.** The hypothesis `hPw1` puts $P$ in the weight-one principal shape: $P = \mathrm{principal}(u_1,a_1,u_2,a_2)$ with $a_1 \neq a_2$. Further, $1 \le k_0$, a natural number $n$ with $n = k_0-1$, and a parity $\varepsilon_0$ are given. The section $S$ on $2\times 3$ real matrices is the conjugate-block Gaussian of matched column degree: $$S(M) = \bigl((M_{00}-iM_{10}) - i(M_{01}-iM_{11})\bigr)\,(M_{02}-iM_{12})^{n}\,\exp\Bigl(-\pi\sum_{i,b}M_{ib}^{2}\Bigr).$$
--
--   **Conclusion.** There exist a real abscissa $\sigma_a$ and a complex number $c \neq 0$ (in the Lean text the constant and the matrix integration variable of the first identity both carry the name `e`, the latter shadowing the former inside the integral) such that the following two identities hold.
--
--   (i) For every $s$ with $\mathrm{Re}\,s > \sigma_a$, the integral over $h \in M_2(\mathbb R)$ of
--   $$\chi_{u_R(w_0)+2,\,a_R(w_0)}(\det h)\,|\det h|^{-2}\cdot \Bigl(\int_{\mathbb R} W_r(\varepsilon_0,\mathrm{default},t)\,W_D\bigl(\mathrm{diag}(at,1)\,h^{-1}\bigr)\,|t|^{\,s-1/2}\,t^{-2}\,dt\Bigr)\cdot\Bigl(\int_{0}^{\infty} y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\,\mathrm{godementInner3}\bigl(\psi_{\infty}\text{-shift by }y,\,S,\,h,\,1\bigr)\,dy\Bigr)$$
--   equals $c$ times the product of $\Gamma_{\mathbb R}(s+\tfrac12+x)$ over the multiset `twistedGammaR K (archOfParamR K P) uR aR` and of $\Gamma_{\mathbb C}(s+\tfrac12+x)$ over the multiset `twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC`. Here $\chi_{u,a}(y)=|y|^{u}$ times $\mathrm{sign}(y)$ when $a \neq 0$; $\mathrm{diag}(y,1)$ is the matrix $\begin{pmatrix}y&0\\0&1\end{pmatrix}$; the Godement inner integral is $\int_{v \in \mathbb R^{2}} S\bigl(h\cdot(\text{rows } m_{0\bullet}+v_0m_{2\bullet},\,m_{1\bullet}+v_1m_{2\bullet})\bigr)\,\psi(-v_1)\,dv$ with $\psi$ the multiplicative shift of $\psi_{\infty}$ by the infinite adele attached to $y$ and $m$ the identity; $\mathrm{archOfParamR}\,K\,P$ is the constant assignment $P$ to every real place and $\mathrm{archOfParamC}\,K\,P$ the constant assignment of the base change of $P$ to every complex place; and the two multisets are the sums, over the real places $w$ of $K$, of the $\Gamma_{\mathbb R}$- (resp. $\Gamma_{\mathbb C}$-) shift multisets of $P$ twisted by $(u_R(w),a_R(w))$, together, in the second case, with the contributions of the complex places $w$ from the base change of $P$ twisted by $(u_C(w),k_C(w))$.
--
--   (ii) For every $s$ with $\mathrm{Re}\,s > \sigma_a$, the iterated integral over $a_2 \in (0,\infty)$ and $a_1 \in \mathbb R$ of the integrand which, when $a_1 \neq 0$ and $a_2>0$, is formed from $q := \begin{pmatrix}a_1&0\\0&a_2\end{pmatrix} \in GL_2(\mathbb R)$ as
--   $$|\det q|\;W_A\bigl(\varepsilon_0,\,w_{0R}\cdot{}^{t}q^{-1}\bigr)\cdot \mathrm{dualWhittakerFn3}\bigl(\mathrm{jacquetVector3}\,D\,u_R(w_0)\,a_R(w_0)\,a\,\psi_{\infty}\,S\bigr)\bigl(\text{archimedean component of }\iota(q)\bigr)\cdot |\det q|^{\,s-1/2}\cdot a_1^{-2},$$
--   and is $0$ otherwise, equals
--   $$\Bigl(\mathrm{archRootNumber}\,K\,(\mathrm{archOfParamR}\,K\,P)\,(\mathrm{archOfParamC}\,K\,P)\,u_R\,a_R\,u_C\,k_C \cdot (-1)^{P.\mathrm{centralSign}.\mathrm{val}} \cdot (-1)^{\#\{\text{complex places of }K\}} \cdot c\Bigr)$$
--   times the product of $\Gamma_{\mathbb R}(s+\tfrac12+x)$ over `twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR` and of $\Gamma_{\mathbb C}(s+\tfrac12+x)$ over the corresponding dual multiset `twistedGammaC` with the dual parameters, $-u_R$, $a_R$, $-u_C$ and $-k_C$; the duals negate the exponents of a parameter while keeping its sign, resp. weight, data, and $\mathrm{archRootNumber}$ is the product of the epsilon factors of the twisted parameters over all infinite places of $K$. In the integrand, ${}^{t}q^{-1}$ denotes [`RSCarrier.transposeInv q`](def/LanglandsTunnell_RSCarrier.html#L31), $\mathrm{dualWhittakerFn3}(W)(g) = W(w_3\cdot{}^{t}g^{-1})$ for the long Weyl element $w_3$ of $GL_3$, $\mathrm{jacquetVector3}$ is $\chi_{u_R(w_0)+1,a_R(w_0)}$ of the determinant of the real matrix of its argument times the integral over $M_2(\mathbb R)$ of `jacquetIntegrand3`, and $\iota(q)$ is the image of $q$ under the embedding of $GL_2(\mathbb R)$ at the real place of $\mathbb Q$ into the adelic $GL_2$, then into the adelic $GL_3$, of which the archimedean component is taken.
--
--   This is the archimedean input for the Rankin–Selberg integral attached to the cubic induction: for a weight-one principal $GL_2(\mathbb R)$ parameter it produces, for the conjugate-block Gaussian section of matched column degree $n=k_0-1$, a single non-zero constant realising both the unfolded torus-pair integral and its dual as the predicted products of $\Gamma_{\mathbb R}$- and $\Gamma_{\mathbb C}$-factors, with the archimedean root number appearing on the dual side. It is used by [`LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen`](thm.html#LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen), where such a section must be exhibited inside the space of polynomial-times-Gaussian sections in order to run the converse theorem for the representation induced from the cubic field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell
open LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3
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
    (w₀R : GL (Fin 2) ℝ) (hw₀R : (w₀R : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0])
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : LanglandsTunnell.Converse.ArchCasimir.IsCasimirEigen D)
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0)
    (hk₀min : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P₂ = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₀ = 0 ∨ k₀ = 1) ∧ ((k₀ : ZMod 2) = a₁ + a₂)) ∧
      (∀ (u : ℂ) (m : ℕ) (hm : 1 ≤ m), P₂ = RealArchParam.discrete u m hm → k₀ = (m : ℤ) + 1))
    (hPw1 : ∃ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ ∧ a₁ ≠ a₂)
    (hk₀ : 1 ≤ k₀)
    (n : ℕ) (hn : (n : ℤ) = k₀ - 1)
    (par₀ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M) :
        ∃ (σa : ℝ) (e : ℂ), e ≠ 0 ∧
        (∀ s : ℂ, σa < s.re →
            (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
              = e * (((twistedGammaR K (archOfParamR K P) uR aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod)) ∧
        (∀ s : ℂ, σa < s.re →
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = ((archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val * (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card) * e) * (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
                    (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod)) := by sorry
