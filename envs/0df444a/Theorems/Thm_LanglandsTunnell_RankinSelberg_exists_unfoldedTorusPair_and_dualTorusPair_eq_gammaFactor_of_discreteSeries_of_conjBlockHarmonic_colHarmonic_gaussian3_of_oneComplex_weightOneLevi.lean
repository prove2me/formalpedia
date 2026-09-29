-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_oneComplex_weightOneLevi
-- name    : LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_oneComplex_weightOneLevi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/93828a69-e477-53ec-93c7-7e2cc0024ba3
-- title:
--   Torus-pair unfolding equals twisted Γ-factors: one complex place, k_ℂ=0
-- statement:
--   Throughout, $K$ is a number field of degree $3$ over $\mathbb Q$ (`_hdeg`), with $\mathcal O_{\mathbb Q}$-algebra structure on $\mathcal O_K$ and $\mathcal O_K$ integral over $\mathcal O_{\mathbb Q}$.
--
--   **The idele class characters.** A homomorphism $\mu\colon \mathbb A_K^\times\to\mathbb C^\times$ is given which is an admissible twist (`_hμ`): it is trivial on the principal ideles, continuous, and of absolute value $1$ everywhere. The hypothesis `_hns` asserts that $\mu$ is not obtained from $\mathbb Q$: there is no admissible twist $\eta$ of $\mathbb A_{\mathbb Q}^\times$ such that for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and with $\eta$ unramified at $p=\mathfrak P\cap\mathcal O_{\mathbb Q}$ one has $\mu(\varpi_{\mathfrak P})=\eta(\varpi_{p})^{f(\mathfrak P/p)}$, where $\varpi$ denotes the uniformiser idele and $f$ the inertia degree `inertiaDeg'`; unramifiedness at a finite place means that the local character is trivial on the units of the valuation ring. The archimedean components of $\mu$ are recorded by functions $u_{\mathbb R},a_{\mathbb R}$ on the real places and $u_{\mathbb C},k_{\mathbb C}$ on the complex places, the hypotheses `huR` and `huC` asserting that at each real place $w$ the local character of $\mu$ on $(K_w)^\times$ is $x\mapsto \|x\|^{m_w u_{\mathbb R}(w)}(x/\|x\|)^{a_{\mathbb R}(w)}$ (with $a_{\mathbb R}(w)\in\mathbb Z/2$ read as an integer) and at each complex place $w$ it is $x\mapsto\|x\|^{m_w u_{\mathbb C}(w)}(x/\|x\|)^{k_{\mathbb C}(w)}$, $m_w$ being the multiplicity of $w$.
--
--   A character $\omega$ of $\mathbb A_{\mathbb Q}^\times$ is given, with `hω` a conjunction of three clauses: $\omega$ is an admissible twist; at every prime $p$ of $\mathcal O_{\mathbb Q}$ which is not a bad place for $(K,\mu)$ — that is, $p$ is neither in `IsRamifiedIn K` nor in `IsTwistRamifiedAbove K μ` — the character $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals `inducedE3 ℚ (inducedCoeff K μ) p`, minus the degree-$3$ coefficient of the induced Euler polynomial built from the coefficients $\mathfrak P\mapsto\mu(\varpi_{\mathfrak P})$ (set to $0$ at ramified $\mathfrak P$); and, for every choice of archimedean data $u_{\mathbb R},a_{\mathbb R},u_{\mathbb C},k_{\mathbb C}$ satisfying the two conditions above for $\mu$, the archimedean component of $\omega$ at the real place of $\mathbb Q$ has exponent $\sum_w u_{\mathbb R}(w)+\sum_w 2u_{\mathbb C}(w)$ and sign exponent $\sum_w a_{\mathbb R}(w)+\sum_w(k_{\mathbb C}(w)+1)$, the sums being finite sums over the real, resp. complex, places of $K$.
--
--   **Adelic auxiliary data.** A monoid homomorphism $E\colon(\mathbb A_{\mathbb Q,\infty})^\times\to\mathbb A_{\mathbb Q}^\times$ splits the infinite part: `hE` says that `infPart (E u) = u` and that the finite part of $E u$ is $1$. A rational number $a$ is given with $a\ne 0$ (`ha`) and $a=-1$ (`ha1`), together with a unit $a_\infty$ of the infinite adele ring whose underlying element is the image of $a$ (`haInf`), and an additive character $\psi_\infty$ of $\mathbb A_{\mathbb Q,\infty}$ equal to $x\mapsto\psi_{\mathrm{arch}}(a x)$ for the standard archimedean character (`hpsiInf`). Measures are fixed: $\nu_{\mathrm{add}}$ on $\mathbb A_{\mathbb Q,\infty}$ equal to $|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the mixed-space ring isomorphism (`hν_add`), and a Haar measure $\nu_{\mathrm{mul}}$ on $(\mathbb A_{\mathbb Q,\infty})^\times$.
--
--   **The $GL_2$ archimedean parameter and its Whittaker data.** A real archimedean parameter $P$ is given, subject to `_hP₁`: if $P$ is principal with exponents $u_1,u_2$ then $|\mathrm{Re}(u_1-u_2)|<1$. Functions $k_w\colon\mathbb Z/2\times\{\text{places of }\mathbb Q\}\to\mathbb Z$, $W_r\colon\mathbb Z/2\times\{\text{places}\}\times\mathbb R\to\mathbb C$ and $W_A\colon\mathbb Z/2\times GL_2(\mathbb R)\to\mathbb C$ are given with the following hypotheses. `hkw1`: in the principal case $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ one has $k_w(\mathrm{par})=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$. `hkw2`: in the discrete case $P=\mathrm{discrete}(u_0,n)$ one has $k_w(\mathrm{par})=n+1$. `hWr1`: if $P$ is principal with $a_1=a_2$ and $\mathrm{par}=a_1$, then $W_r(\mathrm{par},w,-t)=(-1)^{a_1}W_r(\mathrm{par},w,t)$. `hWr2`: if $P$ is discrete then $W_r(\mathrm{par},w,t)=0$ for $t<0$. `hWr3`: if $P$ is principal with $a_1=a_2$ and $\mathrm{par}=a_1+1$, there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (W_r(\mathrm{par},w,t)+(-1)^{a_1}W_r(\mathrm{par},w,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}\,0\,a_1$ at $s$. `hWr4`: for every $\mathrm{par}$ and every $b$ with $b=\mathrm{par}$ or $b=\mathrm{par}+P.\mathrm{centralSign}$, there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the same Mellin transform with $(-1)^{b}$ in place of $(-1)^{a_1}$ converges and equals the archimedean factor of $P.\mathrm{twist}\,0\,b$ at $s$. The function $W_A$ satisfies: `hWAN`, $W_A(\mathrm{par})(u(x)h)=e^{-2\pi i a x}W_A(\mathrm{par})(h)$ for the upper unipotent $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; `hWAZ`, $W_A(\mathrm{par})(zh)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}}W_A(\mathrm{par})(h)$ for scalar $z$; `hWAK`, right equivariance $W_A(\mathrm{par})(h\kappa)=\mathrm{archWeightChar}_{\mathbb R}(k_w(\mathrm{par},\text{default}))(\kappa)\,W_A(\mathrm{par})(h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt`, $W_A(\mathrm{par})(\mathrm{diag}(t,1))=W_r(\mathrm{par},\text{default},t)$ for $t\in\mathbb R^\times$; and `hWAc`, continuity in the $GL_2(\mathbb R)$ variable. Finally $w_{0R}\in GL_2(\mathbb R)$ is the element with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀R`). (Since `hPdisc` below puts $P$ in the discrete series, the clauses conditioned on $P$ being principal are inherited from the general setting.)
--
--   **The Levi datum.** A real place $w_0$ of $K$ is fixed, together with a real archimedean parameter $P_2$ satisfying the branch disjunction `hP₂`: either $K$ has three real places $w_0,w_1,w_2$, pairwise distinct and exhausting the infinite places, and $P_2=\mathrm{principal}(u_{\mathbb R}(w_1),a_{\mathbb R}(w_1),u_{\mathbb R}(w_2),a_{\mathbb R}(w_2))$; or there is a complex place $w_{\mathbb C}$ with $\{w_{\mathbb C},w_0\}$ exhausting the infinite places and either $k_{\mathbb C}(w_{\mathbb C})\ne 0$ and $P_2=\mathrm{discrete}(u_{\mathbb C}(w_{\mathbb C}),|k_{\mathbb C}(w_{\mathbb C})|)$, or $k_{\mathbb C}(w_{\mathbb C})=0$ and $P_2=\mathrm{principal}(u_{\mathbb C}(w_{\mathbb C}),0,u_{\mathbb C}(w_{\mathbb C}),1)$. Further data are an `ArchDatumR P₂` datum $D$ (a Whittaker-type function $D.W$ on $2\times2$ real matrices, smooth on the invertible locus, with the unipotent and central transformation laws of parameter $P_2$, together with the entire completed zeta function, its integral representation, functional equation, finite order and decay data packaged in the structure) and an integer $k_0$ with: `hDW`, $D.W(x\kappa)=\mathrm{archWeightChar}_{\mathbb R}(k_0)(\kappa)D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, the Casimir eigenvalue equation `matrixCasimir (D.W) x = P₂.laplaceEigenvalue * D.W x` for all $x$ of non-zero determinant; `hDnz`, $D.W$ is not identically zero on $GL_2(\mathbb R)$; and `hk₀min`, which requires $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$ when $P_2$ is principal with signs $a_1,a_2$, and $k_0=m+1$ when $P_2=\mathrm{discrete}(u,m)$.
--
--   **The discrete-series specialisation and the branch.** One has $P=\mathrm{discrete}(u_P,n_P)$ with $1\le n_P$ (`hPdisc`), $m=n_P+1$ (`hm`), and natural number $n$ and real $\varepsilon'$ with either $\varepsilon'=-1$ and $n=k_0-m$ or $\varepsilon'=1$ and $n=m-k_0$ (`hcol`). A parity $\mathrm{par}_0\in\mathbb Z/2$ is fixed, and the Schwartz section $S$ on $2\times 3$ real matrices is given explicitly by `hS`:
--   $$S(M)=\bigl((M_{00}-iM_{10})-i(M_{01}-iM_{11})\bigr)^{m}\bigl(M_{02}+\varepsilon' i M_{12}\bigr)^{n}\exp\Bigl(-\pi\sum_{i<2,\ b<3}M_{ib}^2\Bigr).$$
--   The one-sided profile of $W_r$ at the parity $\mathrm{par}_0$ and the place `default` of $\mathbb Q$ is prescribed by `hWpos`, $W_r(\mathrm{par}_0,t)=2t^{u_P+n_P/2+1}e^{-2\pi t}$ for $t>0$, and `hWneg`, $W_r(\mathrm{par}_0,t)=0$ for $t<0$. The branch is pinned down by a complex place $w_{\mathbb C}$ (`hC`), the exhaustion `hall` of the infinite places of $K$ by $w_{\mathbb C}$ and $w_0$, the vanishing `hk0` $k_{\mathbb C}(w_{\mathbb C})=0$, and `hP₂eq` $P_2=\mathrm{principal}(u_{\mathbb C}(w_{\mathbb C}),0,u_{\mathbb C}(w_{\mathbb C}),1)$.
--
--   **Conclusion.** There exist $\sigma_a\in\mathbb R$ and $e\in\mathbb C$ with $e\ne 0$ such that the following two identities hold. (In the first, the variable of the outer integral is itself called `e` in the Lean, ranging over $2\times2$ real matrices; it is written $x$ here, so as to keep it apart from the constant $e$.)
--
--   First, for every $s$ with $\sigma_a<\mathrm{Re}\,s$,
--   $$\int_{x\in\mathbb R^{2\times2}} \mathrm{quasiChar}\bigl(u_{\mathbb R}(w_0)+2,\;a_{\mathbb R}(w_0)\bigr)(\det x)\cdot|\det x|^{-2}\cdot I_1(x,s)\cdot I_2(x,s)\,dx \;=\; e\cdot \Pi(s),$$
--   where $\mathrm{quasiChar}(u,a)(y)=|y|^{u}$ times $1$ if $a=0$ and $\mathrm{sgn}(y)$ otherwise,
--   $$I_1(x,s)=\int_{\mathbb R} W_r(\mathrm{par}_0,\text{default},t)\; D.W\bigl(\mathrm{diag}(a t,1)\,x^{-1}\bigr)\;|t|^{\,s-1/2}\;t^{-2}\,dt,$$
--   $$I_2(x,s)=\int_0^\infty y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\;\mathrm{godementInner3}\bigl(\psi_\infty\!\cdot\!(\text{shift by }y),\,S,\,x,\,1\bigr)\,dy,$$
--   the shift being by the diagonal infinite adele with all components $y$, and $\mathrm{godementInner3}(\psi,S,h,m)=\int_{v\in\mathbb R^2}S\bigl(h\cdot(\text{rows }m_{0\bullet}+v_0m_{2\bullet},\,m_{1\bullet}+v_1m_{2\bullet})\bigr)\psi(-v_1)\,dv$, here with $m$ the identity $3\times3$ matrix; and
--   $$\Pi(s)=\prod_{\chi\in \mathrm{twistedGamma}_{\mathbb R}}\Gamma_{\mathbb R}\bigl(s+\tfrac12+\chi\bigr)\cdot\prod_{\chi\in \mathrm{twistedGamma}_{\mathbb C}}\Gamma_{\mathbb C}\bigl(s+\tfrac12+\chi\bigr)$$
--   with the multisets `twistedGammaR K (archOfParamR K P) uR aR` and `twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC`, that is the multiset sums over the real, resp. real and complex, places of the $\Gamma_{\mathbb R}$- and $\Gamma_{\mathbb C}$-shift multisets of the parameter $P$ (resp. its base change $P.\mathrm{baseChange}$ at complex places) twisted by the local data of $\mu$.
--
--   Secondly, for every $s$ with $\sigma_a<\mathrm{Re}\,s$,
--   $$\int_{a_2>0}\int_{a_1\in\mathbb R} \mathbf 1_{a_1\ne0,\,a_2>0}\;\Bigl(|\det q|\,W_A\bigl(\mathrm{par}_0\bigr)\bigl(w_{0R}\cdot{}^{t}q^{-1}\bigr)\cdot \mathcal W^{\vee}(q)\Bigr)\,|\det q|^{\,s-1/2}\,a_1^{-2}\,da_1\,da_2$$
--   $$=\;\Bigl(\varepsilon_\infty\cdot(-1)^{P.\mathrm{centralSign}}\cdot(-1)^{\#\{\text{complex places of }K\}}\cdot e\Bigr)\cdot\Pi^{\vee}(s),$$
--   where $q=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}\in GL_2(\mathbb R)$ (the integrand being $0$ off the region $a_1\ne0$, $a_2>0$), ${}^tq^{-1}$ is the transpose inverse, and $\mathcal W^{\vee}(q)$ is the value at the archimedean component of the image of $q$ under $GL_2(\mathbb R)\to GL_2(\mathbb A_{\mathbb Q})\to GL_3(\mathbb A_{\mathbb Q})$ (the embedding at the real place of $\mathbb Q$ followed by `iota`, then `archComponent3`) of the dual Whittaker function $g\mapsto F(w_3\cdot{}^tg^{-1})$ attached by `dualWhittakerFn3` to the Jacquet vector $F=\mathrm{jacquetVector3}\,D\,(u_{\mathbb R}(w_0))\,(a_{\mathbb R}(w_0))\,a\,\psi_\infty\,S$, namely $F(g)=\mathrm{quasiChar}(u_{\mathbb R}(w_0)+1,a_{\mathbb R}(w_0))(\det g_\infty)\int_{\mathbb R^{2\times 2}}\mathrm{jacquetIntegrand3}\,D\,(u_{\mathbb R}(w_0))\,(a_{\mathbb R}(w_0))\,a\,\psi_\infty\,S\,g$. Here $\varepsilon_\infty=\mathrm{archRootNumber}\,K\,(\mathrm{archOfParamR}\,K\,P)\,(\mathrm{archOfParamC}\,K\,P)\,u_{\mathbb R}\,a_{\mathbb R}\,u_{\mathbb C}\,k_{\mathbb C}$ is the product over the real places of the epsilon factors of the twisted parameters times the product over the complex places of the epsilon factors of the twisted base-changed parameters, and $\Pi^{\vee}(s)$ is the analogue of $\Pi(s)$ for the dual data: the multisets `twistedGammaR` and `twistedGammaC` formed from the duals of the parameters $P$ and $P.\mathrm{baseChange}$ and the twists $-u_{\mathbb R}$, $a_{\mathbb R}$, $-u_{\mathbb C}$, $-k_{\mathbb C}$.
--
--   This is the archimedean Rankin–Selberg computation for $GL(3)\times GL(2)$ in the Langlands–Tunnell converse-theorem argument for a cubic field $K$, in the Levi branch where $K$ has exactly one complex place $w_{\mathbb C}$ besides the real place $w_0$ and $k_{\mathbb C}(w_{\mathbb C})=0$, so that the Levi parameter is the principal parameter $\mathrm{principal}(u_{\mathbb C},0,u_{\mathbb C},1)$ and the $GL_2$ parameter $P$ is in the discrete series. It identifies both the unfolded torus integral and its dual with one and the same non-zero constant times the twisted archimedean $\Gamma$-factors of the induced parameter, resp. of its dual, and serves as one of the branch cases of the corresponding statement `exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3`, which cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_oneComplex_weightOneLevi.lean

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

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_oneComplex_weightOneLevi
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
    (uP : ℂ) (nP : ℕ) (hnP : 1 ≤ nP) (hPdisc : P = RealArchParam.discrete uP nP hnP)
    (m : ℕ) (hm : m = nP + 1)
    (n : ℕ) (ε' : ℝ) (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (par₀ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (hWpos : ∀ t : ℝ, 0 < t → Wr par₀ default t = (2 : ℂ) * (t : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → Wr par₀ default t = 0)
    (wC : InfinitePlace K) (hC : wC.IsComplex) (hall : ∀ w : InfinitePlace K, w = wC ∨ w = w₀)
    (hk0 : kC wC hC = 0)
    (hP₂eq : P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1) :
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
