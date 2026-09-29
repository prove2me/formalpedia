-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen
-- name    : LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/51abc66c-3442-5033-b400-709fe9315ab5
-- title:
--   Unfolded archimedean torus pair and its dual Γ-factors
-- statement:
--   Throughout, $K$ is a number field with $[K:\mathbb{Q}]=3$ (hypothesis `_hdeg`), equipped with an integral algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$.
--
--   **The character $\mu$ and its archimedean data.** $\mu : (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ is a monoid homomorphism which is an admissible twist (`_hμ`: trivial on the image of $K^\times$, continuous, and of absolute value $1$ everywhere). Hypothesis `_hns` states that $\mu$ does not descend: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and lying over a prime at which $\eta$ is unramified, the value $\mu(\text{uniformiser idele at }\mathfrak{P})$ equals $\eta(\text{uniformiser idele at }\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}})$ raised to the inertia degree of $\mathfrak{P}$. The families $uR, aR$ (indexed by the real places $w$ of $K$, with values in $\mathbb{C}$ and $\mathbb{Z}/2$) and $uC, kC$ (indexed by the complex places, with values in $\mathbb{C}$ and $\mathbb{Z}$) record the archimedean components of $\mu$: hypotheses `huR`, `huC` say that for every place $w$ and every $x \in (K_w)^\times$ the local component of $\mu$ at $w$ equals $\|x\|^{m_w u}\,(x/\|x\|)^{a}$, with $u = uR\,w$, $a = (aR\,w).\mathrm{val}$ in the real case and $u = uC\,w$, $a = kC\,w$ in the complex case.
--
--   **The character $\omega$ of $\mathbb{Q}$.** $\omega : (\mathbb{A}_{\mathbb{Q}})^\times\to\mathbb{C}^\times$ is a monoid homomorphism and `hω` is a threefold conjunction: $\omega$ is an admissible twist; at every prime $p$ which is not a bad place for $(K,\mu)$ (that is, $p$ is neither ramified in $K$ nor twist-ramified above), $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\text{uniformiser idele at }p)$ equals $\mathrm{inducedE3}$ of the coefficient system $\mathfrak{P}\mapsto \mu(\text{uniformiser idele at }\mathfrak{P})$ (zero at ramified $\mathfrak{P}$), i.e. minus the degree-$3$ coefficient of the induced Euler polynomial; and, for every choice of archimedean data $uR,aR,uC,kC$ satisfying the two compatibility conditions above, the archimedean component of $\omega$ at the real place $v$ of $\mathbb{Q}$ has exponent $\sum_{w \text{ real}} uR\,w + \sum_{w\text{ complex}} 2\,uC\,w$ and weight $\sum_{w\text{ real}} (aR\,w).\mathrm{val} + \sum_{w\text{ complex}} (kC\,w + 1)$, the sums being finite sums.
--
--   **Splitting, the additive character, measures.** $E : (\mathbb{A}_{\mathbb{Q},\infty})^\times \to (\mathbb{A}_{\mathbb{Q}})^\times$ is a monoid homomorphism with infinite part the identity and finite part $1$ (`hE`). The rational number $a$ is non-zero (`ha`) and in fact $a=-1$ (`ha1`); $aInf$ is a unit of the infinite adele ring whose underlying element is the image of $a$ (`haInf`); $\psi_\infty$ is the additive character $x\mapsto \psi_{\mathrm{arch}}(a x)$ (`hpsiInf`). The additive measure $\nu_{\mathrm{add}}$ is $|a|^{1/2}$ times the pushforward of Lebesgue measure along the inverse of the identification of the infinite adele ring with the mixed space (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on $(\mathbb{A}_{\mathbb{Q},\infty})^\times$; measurable-space and Borel structures are as registered.
--
--   **The $GL_2(\mathbb{R})$ Whittaker datum attached to $P$.** $P$ is a `RealArchParam`, i.e. either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb{C}$, $a_i\in\mathbb{Z}/2$, or $\mathrm{discrete}(u,n)$ with $1\le n$. Hypothesis `_hP₁` says that if $P$ is principal then $|\mathrm{Re}(u_1-u_2)|<1$. The datum consists of $kw : \mathbb{Z}/2\to \mathrm{InfinitePlace}\,\mathbb{Q}\to\mathbb{Z}$, $Wr : \mathbb{Z}/2\to\mathrm{InfinitePlace}\,\mathbb{Q}\to\mathbb{R}\to\mathbb{C}$ and $WA : \mathbb{Z}/2\to GL_2(\mathbb{R})\to\mathbb{C}$, subject to the following laws, all quantified over the parity $par\in\mathbb{Z}/2$ and (where relevant) over a real place $w$ of $\mathbb{Q}$: `hkw1`, in the principal case $kw\,par\,w = \mathrm{signShift}(a_1+par)+\mathrm{signShift}(a_2+par)$ as a complex number, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$; `hkw2`, in the discrete case $kw\,par\,w = n+1$; `hWr1`, in the principal case with $a_2=a_1$ and $par=a_1$, $Wr\,par\,w(-t)=(-1)^{a_1.\mathrm{val}}Wr\,par\,w(t)$; `hWr2`, in the discrete case $Wr\,par\,w(t)=0$ for $t<0$; `hWr3`, in the principal case with $a_2=a_1$ and $par=a_1+1$, there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (Wr\,par\,w(t)+(-1)^{a_1.\mathrm{val}}Wr\,par\,w(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}\,0\,a_1$ at $s$; `hWr4`, for every $b$ with $b=par$ or $b=par+P.\mathrm{centralSign}$ there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (Wr\,par\,w(t)+(-1)^{b.\mathrm{val}}Wr\,par\,w(-t))/t$ converges and equals the archimedean factor of $P.\mathrm{twist}\,0\,b$ at $s$; `hWAN`, $WA\,par$ transforms under the upper unipotent $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ on the left by $\exp(-2\pi i a x)$; `hWAZ`, $WA\,par$ transforms under the scalar matrix $z\in\mathbb{R}^\times$ on the left by $|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}$; `hWAK`, $WA\,par(h\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(kw\,par\,\mathrm{default})(\kappa)\,WA\,par(h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb{R})$; `hWAt`, $WA\,par(\mathrm{diag}(t,1))=Wr\,par\,\mathrm{default}(t)$ for $t\in\mathbb{R}^\times$; `hWAc`, each $WA\,par$ is continuous. Finally $w_{0R}\in GL_2(\mathbb{R})$ is the element with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀R`).
--
--   **The distinguished real place of $K$, the Levi parameter $P_2$ and its Casimir datum.** $w_0$ is a real place of $K$ (with $h_0$ the witness). $P_2$ is a `RealArchParam` and `hP₂` is the disjunction: either there are two further real places $w_1,w_2$, pairwise distinct from $w_0$ and from each other, exhausting the infinite places of $K$, with $P_2=\mathrm{principal}(uR\,w_1, aR\,w_1, uR\,w_2, aR\,w_2)$; or there is a complex place $w_C$ such that $w_C$ and $w_0$ exhaust the infinite places, and either $kC\,w_C\neq 0$ and $P_2=\mathrm{discrete}(uC\,w_C, |kC\,w_C|)$, or $kC\,w_C=0$ and $P_2=\mathrm{principal}(uC\,w_C,0,uC\,w_C,1)$. The datum $D$ is an `ArchDatumR P₂`: a function $D.W$ on $M_2(\mathbb{R})$, smooth on the invertible locus, satisfying the unipotent law $D.W(\mathrm{unip}(x)g)=\psi(x)D.W(g)$ and the central law $D.W(zg)=\mathrm{centralChar}_{P_2}(z)|z|D.W(g)$, together with an entire zeta function $\mathrm{zetaEntire}$ of $(g,u,a,s)$ whose Mellin-type integral against $D.W$ converges and factors as the archimedean factor of $P_2.\mathrm{twist}\,u\,a$ times $\mathrm{zetaEntire}$, which satisfies the functional equation with $\epsilon$-factor of $P_2.\mathrm{twist}\,u\,a$ relating $(g,u,a,s)$ to $(\mathrm{weyl}\cdot g, -(u+P_2.\mathrm{centralExponent}), a+P_2.\mathrm{centralSign}, 1-s)$, is of finite order in vertical strips, and obeys the stated decay bounds at infinity and at zero. Further, $k_0\in\mathbb{Z}$ and: `hDW`, $D.W(xr)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(r)\,D.W(x)$ for $r$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, $D$ is a Casimir eigenvector, $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all $x$ with $\det x\neq0$, where the eigenvalue is $1/4-((u_1-u_2)/2)^2$ in the principal case and $(1-k^2)/4$ in the discrete case; `hDnz`, $D.W$ is non-zero at some element of $GL_2(\mathbb{R})$; and `hk₀min`, the minimality of the weight: if $P_2$ is principal with parities $a_1,a_2$ then $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, and if $P_2$ is discrete with parameter $m$ then $k_0=m+1$.
--
--   **Conclusion.** There exist a parity $par_0\in\mathbb{Z}/2$ and a function $S$ in `polyGauss3`, that is $S(M)=p(M)\cdot\mathrm{gaussian3}(M)$ for some polynomial $p$ in the six entries of $M\in M_{2\times 3}(\mathbb{R})$, such that, writing $J = \mathrm{jacquetVector3}\,D\,(uR\,w_0)\,(aR\,w_0)\,a\,\psi_\infty\,S$ — the function on $GL_3$ of the infinite adeles given by $g\mapsto \mathrm{quasiChar}(uR\,w_0+1)(aR\,w_0)(\det g_{\mathbb{R}})\cdot\int_{M_2(\mathbb{R})}\mathrm{jacquetIntegrand3}\,D\,(uR\,w_0)\,(aR\,w_0)\,a\,\psi_\infty\,S\,g$ — the following three assertions hold.
--
--   (i) *$SO_2$-weight.* For every $\kappa$ in `rowIsometrySubgroup₀ ℝ` and every $g\in GL_3$ of the infinite adeles,
--   $J\big(g\cdot \mathrm{archComponent3}(\iota(\mathrm{archRealGLAt}\,\kappa))\big)=\mathrm{archWeightChar}_{\mathbb{R}}(kw\,par_0\,\mathrm{default})(\kappa)^{-1}\,J(g)$, where $\kappa$ is embedded at the real place of $\mathbb{Q}$ into adelic $GL_2$, then into adelic $GL_3$ by $\iota$, and finally projected to its archimedean component.
--
--   (ii) *Non-vanishing of the archimedean zeta integral.* There exist an admissible twist $\sigma$ of $\mathbb{Q}$ and $s\in\mathbb{C}$ with $\mathrm{archZeta30}\,\nu_{\mathrm{mul}}\,J\,(\sigma\circ E)\,s\,1\neq 0$, that is $\int_{(\mathbb{A}_{\mathbb{Q},\infty})^\times} J\big(\iota_{GL}(\mathrm{diag}(t,1))\big)\,\sigma(E t)\,\|t\|^{s-1}\,d\nu_{\mathrm{mul}}(t)\neq0$.
--
--   (iii) *The unfolded torus pair and its dual.* There exist an abscissa $\sigma_a\in\mathbb{R}$ and a constant $c\in\mathbb{C}$ with $c\neq 0$ (the constant is written `e` in the statement, a letter also used for the bound $2\times2$ matrix in the first integral) such that both of the following hold for all $s$ with $\mathrm{Re}\,s>\sigma_a$.
--
--   First, with $x$ running over $M_2(\mathbb{R})\cong \mathrm{Fin}\,2\to\mathrm{Fin}\,2\to\mathbb{R}$,
--   $$\int_{M_2(\mathbb{R})} \mathrm{quasiChar}(uR\,w_0+2)(aR\,w_0)(\det x)\,\big(|\det x|^{2}\big)^{-1}\Big(\int_{\mathbb{R}} Wr\,par_0\,\mathrm{default}(t)\;D.W\big(\mathrm{diag}(at,1)\,x^{-1}\big)\,|t|^{\,s-1/2}\,(t^{2})^{-1}\,dt\Big)\Big(\int_0^\infty y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\,\mathrm{godementInner3}\big(\psi_\infty(\cdot\, y),S,x,1\big)\,dy\Big)\,dx$$
--   $$= c\cdot \prod_{\lambda\in \mathrm{twistedGammaR}(K,P,uR,aR)}\Gamma_{\mathbb{R}}(s+\tfrac12+\lambda)\cdot \prod_{\lambda\in \mathrm{twistedGammaC}(K,P,P.\mathrm{baseChange},uR,aR,uC,kC)}\Gamma_{\mathbb{C}}(s+\tfrac12+\lambda),$$
--   where the archimedean parameters are taken to be $P$ at every real place of $K$ and the base change of $P$ at every complex place; $\mathrm{godementInner3}$ is the integral over $v\in\mathbb{R}^2$ of $S\big(x\cdot(\text{rows } m_0+v_0m_2,\;m_1+v_1m_2)\big)$ against $\psi_\infty$ evaluated at $-v_1$ (here $m$ is the identity), and the character in the $y$-integral is the multiplicative shift of $\psi_\infty$ by the image of $y$ in the infinite adeles.
--
--   Second, the dual pairing: with $q=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$,
--   $$\int_{a_2>0}\int_{a_1\in\mathbb{R}} \mathbf{1}_{\{a_1\neq0,\;a_2>0\}}\;|\det q|\;WA\,par_0\big(w_{0R}\cdot {}^{t}q^{-1}\big)\;\big(\mathrm{dualWhittakerFn3}\,J\big)\big(\mathrm{archComponent3}(\iota(\mathrm{archRealGLAt}\,q))\big)\;|\det q|^{\,s-1/2}\,(a_1^{2})^{-1}\,da_1\,da_2$$
--   $$= \Big(\varepsilon_\infty\cdot(-1)^{P.\mathrm{centralSign}.\mathrm{val}}\cdot(-1)^{\#\{w\mid w \text{ complex}\}}\cdot c\Big)\cdot \prod_{\lambda}\Gamma_{\mathbb{R}}(s+\tfrac12+\lambda)\cdot\prod_{\lambda'}\Gamma_{\mathbb{C}}(s+\tfrac12+\lambda'),$$
--   where $\varepsilon_\infty=\mathrm{archRootNumber}(K,P,P.\mathrm{baseChange},uR,aR,uC,kC)$ is the product over the real places of $K$ of the $\epsilon$-factors of $P$ twisted by $(uR\,w,aR\,w)$ times the product over the complex places of the $\epsilon$-factors of the base change of $P$ twisted by $(uC\,w,kC\,w)$, and where $\lambda$ ranges over $\mathrm{twistedGammaR}$ and $\lambda'$ over $\mathrm{twistedGammaC}$ formed from the dual parameters $(\,P.\mathrm{dual}$ at the real places, $(P.\mathrm{baseChange}).\mathrm{dual}$ at the complex places$\,)$ twisted by $(-uR\,w,\,aR\,w)$ and $(-uC\,w,\,-kC\,w)$ respectively. In the second integral $\mathrm{dualWhittakerFn3}\,J(g)=J(\mathrm{longWeyl3}\cdot {}^{t}g^{-1})$ and $q$ is embedded at the real place of $\mathbb{Q}$ exactly as in (i).
--
--   This is the archimedean input of the Rankin–Selberg step in the converse-theorem construction attached to a cubic field $K$ and an idele class character $\mu$ of $K$: it produces a single polynomial-times-Gaussian Schwartz datum whose Jacquet vector has the prescribed $SO_2$-weight, a non-vanishing archimedean $GL_3\times GL_1$ zeta value, and whose unfolded torus pairing and dual torus pairing are the expected products of $\Gamma_{\mathbb{R}}$- and $\Gamma_{\mathbb{C}}$-factors, the dual one with the archimedean root number as constant. It is used by the companion statement in which the Casimir datum is taken of minimal $SO_2$-type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen.lean

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
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda MeasureTheory
open LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen
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
      (∀ (u : ℂ) (m : ℕ) (hm : 1 ≤ m), P₂ = RealArchParam.discrete u m hm → k₀ = (m : ℤ) + 1)) :
    ∃ (par₀ : ZMod 2), ∃ S ∈ polyGauss3,
        (∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
            (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (g * (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) κ))))
              = ((archWeightCharℝ (kw par₀ default) ⟨κ, hκ⟩ : ℂ))⁻¹ * (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) g) ∧
        (∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (σ.comp E) s 1 ≠ 0) ∧
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
