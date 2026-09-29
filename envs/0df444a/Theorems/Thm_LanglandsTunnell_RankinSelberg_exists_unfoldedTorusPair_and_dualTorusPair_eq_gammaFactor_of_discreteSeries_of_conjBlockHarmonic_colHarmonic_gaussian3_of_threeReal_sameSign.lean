-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_threeReal_sameSign
-- name    : LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_threeReal_sameSign
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/076f0df1-7172-59b8-8ce2-2553ba61bafb
-- title:
--   Torus pairs for three real places with equal Levi signs
-- statement:
--   Setting. $K$ is a number field, equipped with an $\mathcal O_{\mathbb Q}$-algebra structure on $\mathcal O_K$ that is integral, and $\operatorname{finrank}_{\mathbb Q} K = 3$ (hypothesis `_hdeg`).
--
--   The character $\mu$ and its archimedean data. $\mu \colon (\mathbb A_K)^\times \to \mathbb C^\times$ is a multiplicative character with `IsAdmissibleTwist K μ`, i.e. $\mu$ is trivial on the image of $K^\times$, continuous, and of absolute value $1$ everywhere. The hypothesis `_hns` is a non-descent condition: there is no admissible twist $\eta$ of $\mathbb Q$ such that, for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and such that $\eta$ is unramified at the prime $\mathfrak p = \mathfrak P \cap \mathcal O_{\mathbb Q}$ below it, one has $\mu(\varpi_{\mathfrak P}) = \eta(\varpi_{\mathfrak p})^{f(\mathfrak P/\mathfrak p)}$, where $\varpi$ denotes the uniformiser idele `uniformizerIdele` and $f$ the inertia degree `inertiaDeg'`. Families $uR, aR$ (indexed by the real places of $K$, with values in $\mathbb C$ and in $\mathbb Z/2$) and $uC, kC$ (indexed by the complex places, with values in $\mathbb C$ and in $\mathbb Z$) are given, and `huR`, `huC` assert `IsArchCompAt K μ w (uR w) ((aR w).val)` at each real place $w$ and `IsArchCompAt K μ w (uC w) (kC w)` at each complex place: for every unit $x$ of the completion $K_w$ the archimedean local character `archLocalChar μ w` takes at $x$ the value $\|x\|^{\,\mathrm{mult}(w)\cdot u}\,(\iota_w(x)/\|x\|)^{a}$ with $\iota_w$ the embedding `extensionEmbedding w`.
--
--   The character $\omega$ of $\mathbb Q$. The hypothesis `hω` has three clauses: $\omega$ is an admissible twist of $\mathbb Q$; for every finite place $p$ of $\mathbb Q$ that is not a bad place for $(K,\mu)$ (that is, neither `IsRamifiedIn K p` nor `IsTwistRamifiedAbove K μ p` holds), $\omega$ is unramified at $p$ and $\mathrm{eulerCoeff}_{\mathbb Q}(\omega,p) = \mathrm{inducedE3}_{\mathbb Q}(\mathrm{inducedCoeff}(K,\mu),p)$, where the left side is $\omega(\varpi_p)$ and the right side is minus the degree-$3$ coefficient of `inducedEulerPoly ℚ (inducedCoeff K μ) p`, the coefficient family being $\mathfrak P \mapsto \mu(\varpi_{\mathfrak P})$ at unramified $\mathfrak P$ and $0$ otherwise; and, for every choice of archimedean data $(uR,aR,uC,kC)$ satisfying the two `IsArchCompAt` conditions above, at each real place $v$ of $\mathbb Q$ the character $\omega$ has archimedean component with exponent $\sum_{w \text{ real}} uR_w + \sum_{w \text{ complex}} 2\,uC_w$ and integer parameter $\sum_{w \text{ real}} (aR_w).\mathrm{val} + \sum_{w \text{ complex}} (kC_w+1)$ (the sums being `finsum`s).
--
--   Adelic and analytic data. $E$ is a monoid homomorphism from the units of the infinite adele ring of $\mathbb Q$ to the units of the full adele ring, splitting the projection in the sense of `hE`: [`M4aHerbrand.infPart (E u) = u`](def/M4aHerbrand_SIdeleClassGroup.html#L25) and [`RatIdele.finPart (E u) = 1`](def/RatIdele_Normalizer.html#L120) for all $u$. A rational number $a$ is given with $a \neq 0$ and $a = -1$, together with a unit $a_\infty$ of the infinite adele ring whose underlying adele is the image of $a$. The additive character $\psi_\infty$ on the infinite adele ring satisfies $\psi_\infty(x) = \psi_{\mathrm{arch}}(a x)$ for the standard archimedean character [`NumberField.StandardAddChar.psiArch`](def/NumberField_StandardGlobalAddCharRat.html#L556). Measures: $\nu_{\mathrm{add}}$ on the infinite adele ring is $|a|^{1/2}$ times the pushforward of Lebesgue measure along the inverse of the ring equivalence `InfiniteAdeleRing.ringEquiv_mixedSpace ℚ`, and $\nu_{\mathrm{mul}}$ is a Haar measure on the units.
--
--   The $GL_2$ archimedean parameter and profiles. $P$ is a real archimedean parameter; `_hP₁` requires $|\operatorname{Re}(u_1-u_2)| < 1$ whenever $P = \mathrm{principal}\,u_1\,a_1\,u_2\,a_2$. Weights $kw$, radial functions $Wr$ and a function $WA$ on $GL_2(\mathbb R)$, each depending on a parity $\mathrm{par} \in \mathbb Z/2$ (and, for $kw$ and $Wr$, on a place of $\mathbb Q$), satisfy: `hkw1`, in the principal case $kw_{\mathrm{par}} = \mathrm{signShift}(a_1+\mathrm{par}) + \mathrm{signShift}(a_2+\mathrm{par})$ with $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$; `hkw2`, in the discrete case $P=\mathrm{discrete}\,u_0\,n$ one has $kw_{\mathrm{par}} = n+1$; `hWr1`, in the principal case with $a_1 = a_2$ and $\mathrm{par} = a_1$, $Wr_{\mathrm{par}}(-t) = (-1)^{a_1.\mathrm{val}} Wr_{\mathrm{par}}(t)$; `hWr2`, in the discrete case $Wr_{\mathrm{par}}$ vanishes on $t<0$; `hWr3`, in the principal case with $a_1=a_2$ and $\mathrm{par}=a_1+1$, for $\operatorname{Re} s$ large the Mellin transform of $t \mapsto (Wr_{\mathrm{par}}(t) + (-1)^{a_1.\mathrm{val}} Wr_{\mathrm{par}}(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}\,0\,a_1$; `hWr4`, for $b = \mathrm{par}$ or $b = \mathrm{par} + P.\mathrm{centralSign}$, the same Mellin transform with $(-1)^{b.\mathrm{val}}$ converges and equals the archimedean factor of $P.\mathrm{twist}\,0\,b$ for $\operatorname{Re} s$ large, where $\mathrm{archFactor}$ is the product of $\Gamma_{\mathbb R}(s+\mu)$ over the multiset `gammaR` times the product of $\Gamma_{\mathbb C}(s+\nu)$ over `gammaC`; `hWAN`, $WA_{\mathrm{par}}(u(x)h) = e^{-2\pi i a x} WA_{\mathrm{par}}(h)$ for the unipotent $u(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$; `hWAZ`, $WA_{\mathrm{par}}(z h) = |z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}} WA_{\mathrm{par}}(h)$ for scalar matrices $z$; `hWAK`, $WA_{\mathrm{par}}(h\kappa) = \mathrm{archWeightChar}_{\mathbb R}(kw_{\mathrm{par}})(\kappa)\, WA_{\mathrm{par}}(h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt`, $WA_{\mathrm{par}}(\mathrm{diagOne}\,t) = Wr_{\mathrm{par}}(t)$; and `hWAc`, $WA_{\mathrm{par}}$ is continuous. Further, $w_{0R} \in GL_2(\mathbb R)$ is the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   The Levi datum. $w_0$ is a real place of $K$, and $P_2$ is a real archimedean parameter satisfying the branch disjunction `hP₂`: either $K$ has three real places $w_0,w_1,w_2$, pairwise distinct and exhausting the infinite places, with $P_2 = \mathrm{principal}\,(uR_{w_1})\,(aR_{w_1})\,(uR_{w_2})\,(aR_{w_2})$, or there is a complex place $w_C$ such that $w_C, w_0$ exhaust the infinite places and either $kC_{w_C} \neq 0$ and $P_2 = \mathrm{discrete}\,(uC_{w_C})\,|kC_{w_C}|$, or $kC_{w_C} = 0$ and $P_2 = \mathrm{principal}\,(uC_{w_C})\,0\,(uC_{w_C})\,1$. $D$ is an `ArchDatumR P₂`, i.e. a real archimedean Whittaker datum for $P_2$ (smooth on the invertible locus, with the unipotent and central transformation laws, an entire zeta function with the stated integral representation, functional equation, finite order and decay properties), $k_0$ is an integer, and: `hDW`, $D.W(x\kappa) = \mathrm{archWeightChar}_{\mathbb R}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, $D$ is a Casimir eigenfunction, $\mathrm{matrixCasimir}(D.W)(x) = P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all invertible $x$; `hDnz`, $D.W$ does not vanish identically; `hk₀min`, in the principal case $k_0 \in \{0,1\}$ and $k_0 \equiv a_1 + a_2 \pmod 2$, and in the discrete case $P_2 = \mathrm{discrete}\,u\,m$ forces $k_0 = m+1$.
--
--   Specialisation. $P = \mathrm{discrete}\,u_P\,n_P$ with $1 \le n_P$, and $m = n_P+1$. A natural number $n$ and a real $\varepsilon'$ satisfy `hcol`: either $\varepsilon' = -1$ and $n = k_0 - m$, or $\varepsilon' = 1$ and $n = m - k_0$. A parity $\mathrm{par}_0 \in \mathbb Z/2$ is given, and the Schwartz section $S$ on $2\times 3$ real matrices is
--   $$S(M) = \bigl((M_{00} - i M_{10}) - i (M_{01} - i M_{11})\bigr)^m \bigl(M_{02} + \varepsilon' i M_{12}\bigr)^n \mathrm{gaussian3}(M),$$
--   with $\mathrm{gaussian3}(M) = \exp(-\pi \sum_{i,b} M_{ib}^2)$. The profile at $\mathrm{par}_0$ and the default place of $\mathbb Q$ is prescribed explicitly: $Wr(t) = 2\,t^{\,u_P + n_P/2 + 1} e^{-2\pi t}$ for $t > 0$ (`hWpos`) and $Wr(t) = 0$ for $t < 0$ (`hWneg`). Finally the Levi branch is fixed: real places $w_1, w_2$ of $K$ with $w_0, w_1, w_2$ pairwise distinct and exhausting the infinite places of $K$, $P_2 = \mathrm{principal}\,(uR_{w_1})\,(aR_{w_1})\,(uR_{w_2})\,(aR_{w_2})$, and equal Levi signs $aR_{w_1} = aR_{w_2}$.
--
--   Conclusion. There exist an abscissa $\sigma_a \in \mathbb R$ and a constant $e \in \mathbb C$ with $e \neq 0$ such that both of the following hold.
--
--   First, for every $s$ with $\sigma_a < \operatorname{Re} s$, the unfolded primal torus pair integral equals $e$ times the twisted $\Gamma$-product of the induced parameter: writing $\eta$ for the integration variable of the outer integral (in the Lean text this bound variable carries the same name as the constant $e$, which it shadows inside the integral), ranging over families $\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb R$ regarded as $2\times 2$ real matrices,
--   $$\int_{\eta} \mathrm{quasiChar}(uR_{w_0}+2)(aR_{w_0})(\det \eta)\cdot |\det \eta|^{-2}\cdot I_1(\eta,s)\cdot I_2(\eta,s) = e\cdot \Pi_{\mathbb R}(s)\cdot \Pi_{\mathbb C}(s),$$
--   where $\mathrm{quasiChar}\,u\,a\,y = |y|^{u}$ times $1$ if $a=0$ and $\operatorname{sign} y$ otherwise,
--   $$I_1(\eta,s) = \int_{\mathbb R} Wr_{\mathrm{par}_0}(t)\, D.W\bigl(\mathrm{diagOne}(a t)\cdot \eta^{-1}\bigr)\,|t|^{\,s-1/2}\,t^{-2}\,dt, \qquad \mathrm{diagOne}(y) = \begin{pmatrix} y & 0\\ 0 & 1\end{pmatrix},$$
--   $$I_2(\eta,s) = \int_0^{\infty} y^{\,P.\mathrm{centralExponent} + P_2.\mathrm{centralExponent} + 2s}\, \mathrm{godementInner3}\bigl(\psi_\infty \cdot \mathrm{mulShift}(\mathrm{ofReal}\,y)\bigr)(S)(\eta)(1)\,dy,$$
--   with $\mathrm{godementInner3}(\psi)(S)(h)(m) = \int_{v \in \mathbb R^2} S\bigl(h\cdot[\,m_{0\bullet}+v_0 m_{2\bullet};\, m_{1\bullet}+v_1 m_{2\bullet}\,]\bigr)\psi(\mathrm{ofReal}(-v_1))\,dv$, and where $\Pi_{\mathbb R}(s)$ is the product of $\Gamma_{\mathbb R}(s+\tfrac12+x)$ over the multiset $\mathrm{twistedGammaR}\,K\,(\mathrm{archOfParamR}\,K\,P)\,uR\,aR$ and $\Pi_{\mathbb C}(s)$ the product of $\Gamma_{\mathbb C}(s+\tfrac12+x)$ over $\mathrm{twistedGammaC}\,K\,(\mathrm{archOfParamR}\,K\,P)\,(\mathrm{archOfParamC}\,K\,P)\,uR\,aR\,uC\,kC$; here $\mathrm{archOfParamR}\,K\,P$ is the constant family with value $P$, $\mathrm{archOfParamC}\,K\,P$ the constant family with value $P.\mathrm{baseChange}$, and the two multisets are the sums over the real, respectively the real and complex, places of the `gammaR` and `gammaC` multisets of the twisted parameters.
--
--   Second, for every $s$ with $\sigma_a < \operatorname{Re} s$, the unfolded dual torus pair integral equals the archimedean root number times $e$ times the dual twisted $\Gamma$-product:
--   $$\int_{a_2 \in (0,\infty)} \int_{a_1 \in \mathbb R} \Bigl[ |\det q|\; WA_{\mathrm{par}_0}\bigl(w_{0R}\cdot {}^{t}q^{-1}\bigr)\cdot \mathcal W^{\vee}\bigl(\iota(q)\bigr)\cdot |\det q|^{\,s-1/2}\cdot a_1^{-2}\Bigr]\,da_1\,da_2$$
--   $$= \Bigl(\mathrm{archRootNumber}\,K\,(\mathrm{archOfParamR}\,K\,P)\,(\mathrm{archOfParamC}\,K\,P)\,uR\,aR\,uC\,kC \cdot (-1)^{P.\mathrm{centralSign}.\mathrm{val}}\cdot(-1)^{\#\{w \text{ complex}\}}\cdot e\Bigr)\cdot \widetilde\Pi_{\mathbb R}(s)\cdot\widetilde\Pi_{\mathbb C}(s).$$
--   Here the inner integrand is defined by the case distinction on $a_1 \neq 0$ and $0 < a_2$, being $0$ when this fails, and in the non-degenerate case $q = \mathrm{upperUnit}\,a_1\,0\,a_2 = \begin{pmatrix} a_1 & 0\\ 0 & a_2\end{pmatrix} \in GL_2(\mathbb R)$; ${}^{t}q^{-1}$ is [`RSCarrier.transposeInv q`](def/LanglandsTunnell_RSCarrier.html#L31); $\mathcal W^{\vee} = \mathrm{dualWhittakerFn3}\bigl(\mathrm{jacquetVector3}\,D\,(uR_{w_0})\,(aR_{w_0})\,a\,\psi_\infty\,S\bigr)$, so that $\mathcal W^{\vee}(g) = \mathrm{jacquetVector3}(\dots)(\mathrm{longWeyl3}\cdot {}^{t}g^{-1})$ with $\mathrm{jacquetVector3}(\dots)(g) = \mathrm{quasiChar}(uR_{w_0}+1)(aR_{w_0})(\det \mathrm{realMat}\,g)\int_{\eta} \mathrm{jacquetIntegrand3}\,D\,(uR_{w_0})\,(aR_{w_0})\,a\,\psi_\infty\,S\,g\,\eta$; and $\iota(q)$ is the image of $q$ under the embedding of $GL_2(\mathbb R)$ at the real place of $\mathbb Q$ into the adelic $GL_2$, followed by `iota` into adelic $GL_3$ and then by the archimedean component map `archComponent3`. The root number $\mathrm{archRootNumber}$ is the product of the epsilon factors of the twisted parameters over the real places times the same product over the complex places; the exponent $\#\{w \text{ complex}\}$ is the cardinality of the set of complex places of $K$; and $\widetilde\Pi_{\mathbb R}(s)$, $\widetilde\Pi_{\mathbb C}(s)$ are the corresponding $\Gamma_{\mathbb R}$- and $\Gamma_{\mathbb C}$-products formed from the dual parameters $(\mathrm{archOfParamR}\,K\,P)^{\vee}$ and $(\mathrm{archOfParamC}\,K\,P)^{\vee}$ with exponents $-uR$, $-uC$, $-kC$ and the same signs $aR$.
--
--   This is the archimedean Rankin–Selberg computation for $GL_3 \times GL_2$ in one branch of the Levi case analysis: the $GL_2$ parameter is a discrete series parameter, the section is the conjugate-block-harmonic times column-harmonic Gaussian $S$, and $K$ has three real places whose two Levi signs agree. It states that the unfolded primal torus integral and its dual counterpart are, up to one and the same non-zero constant $e$ (and, in the dual case, the archimedean root number and explicit signs), the twisted archimedean $\Gamma$-factors of the induced parameter and of its dual. It is one of the branches of the case analysis in [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3), which feeds the archimedean input of the converse theorem used in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_threeReal_sameSign.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_threeReal_sameSign
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
    (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal)
    (h01 : w₀ ≠ w₁) (h02 : w₀ ≠ w₂) (h12 : w₁ ≠ w₂) (hall : ∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂)
    (hP₂eq : P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂))
    (hc : aR w₁ h₁ = aR w₂ h₂) :
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
