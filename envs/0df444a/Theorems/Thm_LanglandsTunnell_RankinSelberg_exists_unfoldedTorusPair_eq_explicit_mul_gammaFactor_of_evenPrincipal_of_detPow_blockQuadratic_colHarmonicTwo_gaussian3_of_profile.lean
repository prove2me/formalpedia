-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_profile
-- name    : LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/3169c0fc-d98b-5d87-b585-2e7922a7e29b
-- title:
--   Unfolded torus pair equals 2π(-1)ᵇρ times Gamma factors
-- statement:
--   The setting is the archimedean frame of the cubic-induction converse-theorem argument. Throughout, $K$ is a number field whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, with $[K:\mathbb{Q}]=3$ (`_hdeg`).
--
--   **Global frame.** A homomorphism $\mu\colon (\mathbb{A}_K)^\times\to\mathbb{C}^\times$ is given which is an admissible twist (`_hμ`), i.e. trivial on the image of $K^\times$, continuous, and of absolute value $1$ everywhere. The hypothesis `_hns` asserts that $\mu$ is not a base change: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and with $\eta$ unramified at the prime $p=\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ below it one has $\mu(\varpi_{\mathfrak{P}})=\eta(\varpi_{p})^{f}$, $f$ the inertia degree of $\mathfrak{P}$ over $p$ (unramifiedness being the condition that the local character of $\mu$ be trivial on the units of the valuation ring, and $\varpi$ the idele with a uniformiser in the chosen place and $1$ elsewhere). Families $uR,aR$ (indexed by the real places of $K$) and $uC,kC$ (indexed by the complex places) record the archimedean exponents of $\mu$: `huR` says that at each real place $w$ the archimedean local component of $\mu$ on $x$ is $\|x\|^{m_w\,uR_w}\,(x/\|x\|)^{(aR_w).\mathrm{val}}$, and `huC` the corresponding identity at each complex place with exponents $uC_w,kC_w$. A character $\omega$ of $(\mathbb{A}_{\mathbb{Q}})^\times$ is given with `hω` of three clauses: $\omega$ is an admissible twist; at every rational prime $p$ which is not bad for $(K,\mu)$ — bad meaning either that some prime of the fibre over $p$ has ramification index $\neq 1$, or that $\mu$ is ramified at some prime above $p$ — the character $\omega$ is unramified and its Euler coefficient $\omega(\varpi_p)$ equals `inducedE3 ℚ (inducedCoeff K μ) p`, minus the degree-$3$ coefficient of the induced Euler polynomial formed from the coefficients $\mu(\varpi_{\mathfrak{P}})$ at the unramified primes above $p$ (and $0$ at the ramified ones); and, for every choice of archimedean exponent data for $\mu$ as above, at the real place $v$ of $\mathbb{Q}$ the archimedean component of $\omega$ has exponent $\sum_{w\ \mathrm{real}} uR_w+\sum_{w\ \mathrm{complex}} 2\,uC_w$ and integer exponent $\sum_{w\ \mathrm{real}}(aR_w).\mathrm{val}+\sum_{w\ \mathrm{complex}}(kC_w+1)$. A splitting $E\colon (\mathbb{A}_{\mathbb{Q},\infty})^\times\to(\mathbb{A}_{\mathbb{Q}})^\times$ is given with `hE`: the infinite part of $E(u)$ is $u$ and its finite part is $1$. The additive parameter is $a\in\mathbb{Q}^\times$ with $a=-1$ (`ha`, `ha1`), together with a unit $a_\infty$ of the infinite adele ring mapping to $a$ (`haInf`) and the additive character $\psi_\infty$ with $\psi_\infty(x)=\psi_{\mathrm{arch}}(a\,x)$ (`hpsiInf`). Measurable and Borel structures on $\mathbb{A}_{\mathbb{Q},\infty}$ and on its unit group are fixed; $\nu_{\mathrm{add}}$ is the measure $|a|^{1/2}$ times the pushforward of Lebesgue measure along the inverse of the mixed-space ring equivalence (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on $(\mathbb{A}_{\mathbb{Q},\infty})^\times$.
--
--   **The archimedean parameter of the $\mathbb{Q}$-side form.** $P$ is a real archimedean parameter, either principal $(u_1,a_1,u_2,a_2)$ or discrete $(u,k)$ with $k\geq 1$, subject to `_hP₁`: in the principal case $|\mathrm{Re}(u_1-u_2)|<1$. Data $kw$ (weights), $Wr$ (functions on $\mathbb{R}$) and $WA$ (functions on $GL_2(\mathbb{R})$), all indexed by a parity $\mathrm{par}\in\mathbb{Z}/2$ and, for $kw,Wr$, by an infinite place of $\mathbb{Q}$, are given with the following hypotheses. `hkw1`: in the principal case $kw_{\mathrm{par}}=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$; `hkw2`: in the discrete case of weight $n$, $kw_{\mathrm{par}}=n+1$. `hWr1`: if $P$ is principal with equal signs $a_1$ and $\mathrm{par}=a_1$, then $Wr_{\mathrm{par}}(-t)=(-1)^{a_1.\mathrm{val}}Wr_{\mathrm{par}}(t)$; `hWr2`: in the discrete case $Wr_{\mathrm{par}}$ vanishes on the negative reals. `hWr3`: if $P$ is principal with equal signs $a_1$ and $\mathrm{par}=a_1+1$, there is an abscissa beyond which the Mellin transform of $t\mapsto (Wr_{\mathrm{par}}(t)+(-1)^{a_1.\mathrm{val}}Wr_{\mathrm{par}}(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P$ twisted by $(0,a_1)$ at $s$; `hWr4`: for every $\mathrm{par}$ and every $b'$ with $b'=\mathrm{par}$ or $b'=\mathrm{par}+P.\mathrm{centralSign}$, there is an abscissa beyond which the Mellin transform of $t\mapsto (Wr_{\mathrm{par}}(t)+(-1)^{b'.\mathrm{val}}Wr_{\mathrm{par}}(-t))/t$ converges and equals the archimedean factor of $P$ twisted by $(0,b')$ at $s$. The Whittaker transformation laws for $WA$ are: `hWAN`, $WA_{\mathrm{par}}(n(x)h)=e^{-2\pi i a x}WA_{\mathrm{par}}(h)$ for the unipotent $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; `hWAZ`, $WA_{\mathrm{par}}(z\cdot h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}WA_{\mathrm{par}}(h)$ for scalar $z$; `hWAK`, right equivariance under the subgroup `rowIsometrySubgroup₀ ℝ` by the weight character `archWeightCharℝ` of weight $kw_{\mathrm{par}}$ at the infinite place `default` of $\mathbb{Q}$; `hWAt`, $WA_{\mathrm{par}}(\mathrm{diag}(t,1))=Wr_{\mathrm{par},\mathrm{default}}(t)$ for $t\in\mathbb{R}^\times$; and `hWAc`, continuity of each $WA_{\mathrm{par}}$. Finally $w_{0R}\in GL_2(\mathbb{R})$ has matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀R`).
--
--   **The companion parameter and datum.** $w_0$ is a real place of $K$. The parameter $P_2$ satisfies `hP₂`: either $K$ has exactly three infinite places $w_0,w_1,w_2$, all real and pairwise distinct, and $P_2$ is principal $(uR_{w_1},aR_{w_1},uR_{w_2},aR_{w_2})$; or the infinite places of $K$ are exactly $w_0$ and one complex place $w_C$, and then either $kC_{w_C}\neq 0$ and $P_2$ is discrete with parameter $uC_{w_C}$ and weight $|kC_{w_C}|$, or $kC_{w_C}=0$ and $P_2$ is principal $(uC_{w_C},0,uC_{w_C},1)$. $D$ is an `ArchDatumR P₂`, that is a function $D.W$ on $2\times 2$ real matrices which is smooth on the invertible locus, satisfies the unipotent law $D.W(n(x)g)=\psi(x)D.W(g)$ and the central law $D.W(zg)=\mathrm{centralChar}_{P_2}(z)\,|z|\,D.W(g)$, and carries the package of entire zeta functions: an entire $\mathrm{zetaEntire}$ in $s$ for each $(g,u,a)$, an abscissa past which the zeta integrand $y\mapsto D.W(\mathrm{diag}(y,1)g)\,|y|^{u}(\mathrm{sgn}\,y)^{[a\neq 0]}|y|^{s-1}|y|^{-1}$ is integrable with integral equal to the archimedean factor of $P_2$ twisted by $(u,a)$ times $\mathrm{zetaEntire}$, a local functional equation under $g\mapsto wg$, $(u,a,s)\mapsto(-(u+P_2.\mathrm{centralExponent}),a+P_2.\mathrm{centralSign},1-s)$ with constant the $\varepsilon$-factor of the twist, finite order in vertical strips, and the decay bounds for all derivatives at large and small $|y|$ along the Iwasawa coordinates. An integer $k_0$ is given with `hDW`: $D.W(x\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in the row-isometry subgroup; `hDE`: $D$ is a Casimir eigenvector, $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for $\det x\neq 0$; `hDnz`: $D.W$ does not vanish identically; and `hk₀min`: in the principal case $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, in the discrete case of weight $m$, $k_0=m+1$.
--
--   **The specialisation.** Complex numbers $\nu_1,\nu_2$ and $b\in\mathbb{Z}/2$ are given with $P=\mathrm{principal}(\nu_1,b,\nu_2,b)$ (`hPev`, the even principal case); $k_0=0$ (`hk₀`); `hLevi`: if $P_2$ is principal with signs $a_1,a_2$ then $a_1=b+1$; $\delta\in\{0,1\}$ with $\delta\equiv aR_{w_0}+b \pmod 2$ (`hδ`, `hδpar`); and the Schwartz section $S$ on $2\times 3$ real matrices is given explicitly (`hS`) by
--   $$S(M)=(M_{00}M_{11}-M_{01}M_{10})^{\delta}\,\bigl((M_{00}+iM_{10})^2+(M_{01}+iM_{11})^2\bigr)\,(M_{02}-iM_{12})^2\,e^{-\pi\sum_{i,b}M_{ib}^2}.$$
--   Further, $u_1,u_2\in\mathbb{C}$ and $c\in\mathbb{Z}/2$ with $P_2=\mathrm{principal}(u_1,c,u_2,c)$ (`hP₂eq`), and $\rho\in\mathbb{C}$ realises the weight-zero Levi profile of $D$ (`hρ`): for all $\tau>0$,
--   $$D.W(\mathrm{diag}(\tau,1))=\rho\,\tau\cdot 4\int_{0}^{\infty} r^{u_1}e^{-\pi r^2}\,(\tau/r)^{u_2}e^{-\pi(\tau/r)^2}\,\frac{dr}{r}.$$
--
--   **Conclusion.** There exists $\sigma_a\in\mathbb{R}$ such that for every $s\in\mathbb{C}$ with $\mathrm{Re}\,s>\sigma_a$,
--   $$\int_{e\in\mathbb{R}^{2\times 2}} |\det e|^{\,uR_{w_0}+2}(\mathrm{sgn}\det e)^{[aR_{w_0}\neq 0]}\,|\det e|^{-2}\,\Bigl(\int_{\mathbb{R}}Wr_{b,\mathrm{default}}(t)\,D.W\bigl(\mathrm{diag}(at,1)\,e^{-1}\bigr)\,|t|^{\,s-1/2}\,t^{-2}\,dt\Bigr)\cdot\Bigl(\int_{0}^{\infty}y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\,\mathrm{godementInner3}\bigl(\psi_\infty\!\cdot\!\mathrm{mulShift}(y),S,e,1\bigr)\,dy\Bigr)\,de$$
--   equals
--   $$\bigl(2\pi\,(-1)^{b.\mathrm{val}}\,\rho\bigr)\cdot\prod_{x\in\Gamma_{\mathbb{R}}\text{-multiset}}\Gamma_{\mathbb{R}}\bigl(s+\tfrac12+x\bigr)\cdot\prod_{x\in\Gamma_{\mathbb{C}}\text{-multiset}}\Gamma_{\mathbb{C}}\bigl(s+\tfrac12+x\bigr),$$
--   where the first multiset is `twistedGammaR K (archOfParamR K P) uR aR`, the sum over the real places $w$ of $K$ of the $\Gamma_{\mathbb{R}}$-multiset of $P$ twisted by $(uR_w,aR_w)$, namely $\{\nu_1+uR_w+\mathrm{signShift}(b+aR_w),\ \nu_2+uR_w+\mathrm{signShift}(b+aR_w)\}$, and the second is `twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC`, the sum of the (empty, $P$ being principal) $\Gamma_{\mathbb{C}}$-contributions of the real places and, over the complex places $w$, of the $\Gamma_{\mathbb{C}}$-multisets of the base change $\langle\nu_1,0,\nu_2,0\rangle$ of $P$ twisted by $(uC_w,kC_w)$. In the inner integral over $e$, $\mathrm{diag}(at,1)$ is the matrix $\begin{pmatrix}at&0\\0&1\end{pmatrix}$ and $\mathrm{godementInner3}(\psi,S,h,m)=\int_{v\in\mathbb{R}^2}S\bigl(h\cdot[\,m_{0\bullet}+v_0m_{2\bullet};\,m_{1\bullet}+v_1m_{2\bullet}\,]\bigr)\,\psi(-v_1)$, the character being $\psi_\infty$ shifted multiplicatively by the real number $y$ placed at the infinite place of $\mathbb{Q}$, and $m$ the identity $3\times 3$ matrix. Thus the assertion is the evaluation of the unfolded torus pair in closed form, with the proportionality constant identified as $2\pi(-1)^{b}\rho$ rather than merely asserted to exist.
--
--   This is the primal half of the archimedean Rankin–Selberg computation for the cubic induction: it evaluates the unfolded torus integral attached to the $GL_2\times GL_3$ section $\det^{\delta}(z_0^2+z_1^2)(M_{02}-iM_{12})^2$ times the Gaussian, in the case of an even principal parameter $P$ and a weight-zero Levi profile of opposite parity for the companion datum, as an explicit constant times the twisted $\Gamma_{\mathbb{R}}$- and $\Gamma_{\mathbb{C}}$-factors of the expected archimedean $L$-factor. It feeds the combined primal-and-dual statement `exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3`, which supplies the archimedean input to the converse theorem identifying the induced Hecke eigensystem with an automorphic form on $GL_2/\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_profile.lean

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
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda
open MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_profile
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
    (ν₁ ν₂ : ℂ) (b : ZMod 2) (hPev : P = RealArchParam.principal ν₁ b ν₂ b)
    (hk₀ : k₀ = 0)
    (hLevi : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P₂ = RealArchParam.principal u₁ a₁ u₂ a₂ → a₁ = b + 1)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = aR w₀ h₀ + b)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) ^ 2 + (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ)) ^ 2) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ 2) * gaussian3 M)

    (u₁ u₂ : ℂ) (c : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c u₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((τ) / r : ℝ) : ℂ) ^ (u₂) * (Real.exp (-(Real.pi * ((τ) / r) ^ 2)) : ℂ)) / (r : ℂ))) :
    ∃ σa : ℝ, ∀ s : ℂ, σa < s.re →
            (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr b default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
              = ((((2 * Real.pi : ℝ) : ℂ) * (-1 : ℂ) ^ b.val) * ρ) * (((twistedGammaR K (archOfParamR K P) uR aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod) := by sorry
