-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/d99d945c-a90c-5d65-b45d-645cfcaeccf3
-- title:
--   Even principal parameter: primal and dual unfolded torus-pair identities
-- statement:
--   Throughout, $K$ is a number field with $[K:\mathbb{Q}]=3$ (hypothesis `_hdeg`), equipped with an $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_K$ which is integral, and $\mu:(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ is a character which is an *admissible twist* (`_hμ`): trivial on the principal ideles $K^\times$, continuous, and of absolute value $1$ everywhere. The hypothesis `_hns` says that $\mu$ is not comparable with a character of $\mathbb{Q}$: there is no admissible twist $\eta$ of $(\mathbb{A}_{\mathbb{Q}})^\times$ such that for every $\mathfrak{P}\in\operatorname{Spec}^1(\mathcal{O}_K)$ at which $\mu$ is unramified and such that $\eta$ is unramified at the place $p$ below $\mathfrak{P}$, one has $\mu(\varpi_{\mathfrak{P}})=\eta(\varpi_p)^{f(\mathfrak{P}/p)}$, where $\varpi$ denotes the uniformiser idele and $f$ the inertia degree; unramifiedness at a finite place means that the local component kills the local units.
--
--   Archimedean parameters of $\mu$: functions $uR,aR$ on the real places and $uC,kC$ on the complex places of $K$ (values in $\mathbb{C}$, $\mathbb{Z}/2$, $\mathbb{C}$, $\mathbb{Z}$ respectively), with `huR`, `huC` asserting `IsArchCompAt`, i.e. at each real place $w$ the local component of $\mu$ on $(K_w)^\times$ is $x\mapsto \|x\|^{m_w\,uR(w)}\,(x/\|x\|)^{aR(w).\mathrm{val}}$ and at each complex place $w$ it is $x\mapsto \|x\|^{m_w\,uC(w)}(x/\|x\|)^{kC(w)}$, $m_w$ being the multiplicity of $w$.
--
--   The character $\omega$ on $(\mathbb{A}_{\mathbb{Q}})^\times$ comes with the threefold hypothesis `hω`: (a) $\omega$ is an admissible twist of $\mathbb{Q}$; (b) at every finite place $p$ of $\mathbb{Q}$ which is not bad for $(K,\mu)$ — bad meaning ramified in $K$ or twist-ramified above $p$ — $\omega$ is unramified and its Euler coefficient $\omega(\varpi_p)$ equals $\mathrm{inducedE3}$ of the coefficient system $\mathfrak{P}\mapsto\mu(\varpi_{\mathfrak{P}})$ (zero at ramified $\mathfrak{P}$), namely minus the degree-$3$ coefficient of the induced Euler polynomial at $p$; (c) for *any* data $uR,aR,uC,kC$ satisfying the two `IsArchCompAt` conditions above and any real place $v$ of $\mathbb{Q}$, the archimedean component of $\omega$ at $v$ has exponent $\sum_{w\ \mathrm{real}}uR(w)+\sum_{w\ \mathrm{complex}}2\,uC(w)$ and sign/weight exponent $\sum_{w\ \mathrm{real}}aR(w).\mathrm{val}+\sum_{w\ \mathrm{complex}}(kC(w)+1)$ (finite sums over the places).
--
--   Adelic normalisations: $E$ is a monoid homomorphism from the infinite idele units to the idele units splitting the infinite part, `hE` requiring $\mathrm{infPart}(E u)=u$ and trivial finite part; $a\in\mathbb{Q}$ is nonzero and equal to $-1$ (`ha`, `ha1`); $a_{\infty}$ is an infinite idele unit with coordinate $a$ (`haInf`); $\psi_\infty$ is the additive character $x\mapsto \psi_{\mathrm{arch}}(a\,x)$ of the infinite adele ring (`hpsiInf`), $\psi_{\mathrm{arch}}$ being the standard archimedean character; $\nu_{\mathrm{add}}$ is the measure $|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the identification of the infinite adele ring with the mixed space (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on the infinite idele units.
--
--   The $\mathrm{GL}_2$ archimedean parameter is $P:\mathrm{RealArchParam}$, either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u,k)$ with $k\ge 1$; `_hP₁` requires that in every principal presentation $|\mathrm{Re}(u_1-u_2)|<1$. Attached to $P$ are a weight function $kw:\mathbb{Z}/2\times\mathrm{InfinitePlace}(\mathbb{Q})\to\mathbb{Z}$, radial functions $Wr(\mathrm{par},w):\mathbb{C}\to\mathbb{C}$ and Whittaker functions $WA(\mathrm{par}):\mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$, subject to the following groups of hypotheses. Weights: `hkw1`, in the principal case $kw(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ with $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$; `hkw2`, in the discrete case of weight $n$, $kw(\mathrm{par},w)=n+1$. Radial symmetry and Mellin behaviour: `hWr1`, for $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1$, $Wr(\mathrm{par},w)(-t)=(-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w)(t)$; `hWr2`, in the discrete case $Wr(\mathrm{par},w)$ vanishes on $t<0$; `hWr3`, for $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1+1$ there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (Wr(\mathrm{par},w)(t)+(-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w)(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}\,\mathrm{archFactor}(P.\mathrm{twist}\,0\,a_1)(s)$, where the arch factor of a real parameter is the product of $\Gamma_{\mathbb{R}}(s+\mu)$ over its `gammaR` multiset times the product of $\Gamma_{\mathbb{C}}(s+\nu)$ over its `gammaC` multiset; `hWr4`, for every $b'$ with $b'=\mathrm{par}$ or $b'=\mathrm{par}+P.\mathrm{centralSign}$ the same symmetrised Mellin transform, with $(-1)^{b'.\mathrm{val}}$, converges for $\mathrm{Re}\,s$ large and equals $\mathrm{archFactor}(P.\mathrm{twist}\,0\,b')(s)$. Transformation laws of $WA$: `hWAN`, $WA(\mathrm{par})(u(x)h)=\exp(-2\pi i a x)\,WA(\mathrm{par})(h)$ for the unipotent $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; `hWAZ`, $WA(\mathrm{par})(zh)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}\,WA(\mathrm{par})(h)$ for scalar $z$, where the central exponent is $u_1+u_2$ (principal) or $2u$ (discrete) and the central sign is $a_1+a_2$ (principal) or $k+1$ (discrete); `hWAK`, right equivariance $WA(\mathrm{par})(h\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(kw(\mathrm{par},\ast))(\kappa)\,WA(\mathrm{par})(h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`, the weight being taken at the default place; `hWAt`, $WA(\mathrm{par})(\mathrm{diag}(t,1))=Wr(\mathrm{par},\mathrm{default})(t)$ for $t\in\mathbb{R}^\times$; `hWAc`, continuity of each $WA(\mathrm{par})$. Finally $w_{0,\mathbb{R}}\in\mathrm{GL}_2(\mathbb{R})$ is the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀R`).
--
--   On the side of $K$: $w_0$ is a real place of $K$, and $P_2$ is a real archimedean parameter satisfying the place-profile hypothesis `hP₂`: either $K$ has three real places $w_0,w_1,w_2$, pairwise distinct and exhausting the infinite places, and $P_2=\mathrm{principal}(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$; or $K$ has one complex place $w_C$ and the infinite places are exactly $w_C,w_0$, and either $kC(w_C)\neq 0$ and $P_2=\mathrm{discrete}(uC(w_C),|kC(w_C)|)$, or $kC(w_C)=0$ and $P_2=\mathrm{principal}(uC(w_C),0,uC(w_C),1)$. Next, $D$ is an `ArchDatumR P₂` — a Whittaker datum on $\mathrm{GL}_2(\mathbb{R})$ consisting of a function $D.W$ on $2\times 2$ real matrices, smooth on the invertible locus, with the unipotent law $D.W(u(x)g)=\psi(x)D.W(g)$ and central law $D.W(zg)=\mathrm{centralChar}(P_2)(z)\,|z|\,D.W(g)$, together with entire zeta functions, their integral representation by $\mathrm{archFactor}$ of twists of $P_2$, a functional equation with $\epsilon$-factor of the twist, finite order in vertical strips and decay estimates at $|y|\ge1$ and $0<|y|\le1$ — and $k_0\in\mathbb{Z}$, with: `hDW`, right equivariance of $D.W$ under `rowIsometrySubgroup₀ ℝ` by $\mathrm{archWeightChar}_{\mathbb{R}}(k_0)$; `hDE`, $D$ is a Casimir eigenfunction, $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all $x$ with $\det x\neq 0$, the eigenvalue being $\frac14-((u_1-u_2)/2)^2$ in the principal case and $(1-k^2)/4$ in the discrete case; `hDnz`, $D.W$ does not vanish identically on $\mathrm{GL}_2(\mathbb{R})$; `hk₀min`, in the principal case $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2 \pmod 2$, and in the discrete case of weight $m$, $k_0=m+1$.
--
--   The case-distinguishing hypotheses are: `hPev`, $P=\mathrm{principal}(\nu_1,b,\nu_2,b)$ is *even principal* for some $\nu_1,\nu_2\in\mathbb{C}$ and $b\in\mathbb{Z}/2$; `hk₀`, $k_0=0$; `hLevi`, in every principal presentation of $P_2$ the first sign is $b+1$. Finally $\delta\in\mathbb{N}$ with $\delta\in\{0,1\}$ (`hδ`) and $\delta\equiv aR(w_0)+b\pmod 2$ (`hδpar`), and $S$ is the Schwartz section on $2\times3$ real matrices given by `hS`:
--   $$S(M)=(M_{00}M_{11}-M_{01}M_{10})^{\delta}\,\bigl((M_{00}+iM_{10})^{2}+(M_{01}+iM_{11})^{2}\bigr)\,\bigl(M_{02}-iM_{12}\bigr)^{2}\,\exp\Bigl(-\pi\sum_{i,b}M_{ib}^{2}\Bigr).$$
--
--   The conclusion asserts the existence of an abscissa $\sigma_a\in\mathbb{R}$ and of a nonzero complex constant (the existential variable `e`; it is written $c$ below, since inside the first integral the Lean integration variable over $2\times 2$ real matrices is also named `e`) such that the following two identities hold.
--
--   First, for every $s$ with $\sigma_a<\mathrm{Re}\,s$,
--   $$\int_{M_2(\mathbb{R})}\chi_{uR(w_0)+2,\,aR(w_0)}(\det e)\,|\det e|^{-2}\Bigl(\int_{\mathbb{R}}Wr(b,\mathrm{default})(t)\,D.W\bigl(\mathrm{diag}(at,1)\,e^{-1}\bigr)\,|t|^{\,s-\frac12}\,t^{-2}\,dt\Bigr)\Bigl(\int_{0}^{\infty}y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\,G(y,e)\,dy\Bigr)de$$
--   equals $c$ times the product of $\Gamma_{\mathbb{R}}(s+\tfrac12+x)$ over the multiset $\mathrm{twistedGammaR}$ of $K$ for the constant parameter family $P$ and the twisting data $uR,aR$, times the product of $\Gamma_{\mathbb{C}}(s+\tfrac12+x)$ over the corresponding multiset $\mathrm{twistedGammaC}$, the latter collecting the `gammaC` multisets of $P.\mathrm{twist}(uR(w),aR(w))$ over the real places $w$ of $K$ and those of $P.\mathrm{baseChange}.\mathrm{twist}(uC(w),kC(w))$ over the complex places. Here $\chi_{u,a}(y)=|y|^{u}$ times $1$ if $a=0$ and $\mathrm{sign}(y)$ otherwise; $\mathrm{diag}(\tau,1)$ denotes `ArchR.diagOne`; and $G(y,e)$ is the Godement inner integral $\mathrm{godementInner3}$ of the shifted character $x\mapsto\psi_\infty(y\,x)$, of $S$, of $e$ and of the identity $3\times3$ matrix, namely
--   $$G(y,e)=\int_{\mathbb{R}^2}S\Bigl(e\cdot\begin{pmatrix}1&0&v_0\\0&1&v_1\end{pmatrix}\Bigr)\,\psi_\infty\bigl(y\cdot(-v_1)\bigr)\,dv.$$
--
--   Second, for every $s$ with $\sigma_a<\mathrm{Re}\,s$, the iterated integral over $a_2\in(0,\infty)$ and $a_1\in\mathbb{R}$ of the integrand which vanishes unless $a_1\neq0$ and $a_2>0$, and which in that case, with $q=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}\in\mathrm{GL}_2(\mathbb{R})$ (the `upperUnit` matrix with middle entry $0$), equals
--   $$|\det q|\cdot WA(b)\bigl(w_{0,\mathbb{R}}\,(q^{-1})^{\mathsf T}\bigr)\cdot \mathrm{dualWhittakerFn3}\bigl(\mathrm{jacquetVector3}\,D\,uR(w_0)\,aR(w_0)\,a\,\psi_\infty\,S\bigr)(g_q)\cdot|\det q|^{\,s-\frac12}\cdot a_1^{-2},$$
--   is equal to $\bigl(\mathrm{archRootNumber}\cdot(-1)^{P.\mathrm{centralSign}.\mathrm{val}}\cdot(-1)^{\#\{\text{complex places of }K\}}\bigr)\cdot c$ times the product of $\Gamma_{\mathbb{R}}(s+\tfrac12+x)$ over $\mathrm{twistedGammaR}$ for the dualised parameters $w\mapsto P.\mathrm{dual}$ and the data $-uR,aR$, times the product of $\Gamma_{\mathbb{C}}(s+\tfrac12+x)$ over $\mathrm{twistedGammaC}$ for the dualised real and complex parameters and the data $-uR,aR,-uC,-kC$. Here $\mathrm{archRootNumber}$ is formed from the constant families $w\mapsto P$, $w\mapsto P.\mathrm{baseChange}$ and the data $uR,aR,uC,kC$, i.e. the product over the real places of $K$ of the $\epsilon$-factor of $P.\mathrm{twist}(uR(w),aR(w))$ times the product over the complex places of the $\epsilon$-factor of $P.\mathrm{baseChange}.\mathrm{twist}(uC(w),kC(w))$; $(q^{-1})^{\mathsf T}$ is [`RSCarrier.transposeInv`](def/LanglandsTunnell_RSCarrier.html#L31); $g_q$ is the archimedean $\mathrm{GL}_3$-component of the image of $q$ under the embedding of $\mathrm{GL}_2(\mathbb{R})$ at the real place of $\mathbb{Q}$ into the adelic $\mathrm{GL}_2$ followed by the cubic inclusion $\iota$ into the adelic $\mathrm{GL}_3$; $\mathrm{dualWhittakerFn3}(W)(g)=W(w_{3}\,{}^{t}g^{-1})$ with $w_3$ the long Weyl element and ${}^{t}g^{-1}$ the transpose-inverse in $\mathrm{GL}_3$; and $\mathrm{jacquetVector3}\,D\,u_3\,a_3\,a\,\psi\,S\,(g)=\chi_{u_3+1,a_3}(\det g_{\mathbb{R}})\int_{M_2(\mathbb{R})}\mathrm{jacquetIntegrand3}\,D\,u_3\,a_3\,a\,\psi\,S\,g\,e\,de$.
--
--   This is the archimedean Rankin–Selberg computation for the pair $\mathrm{GL}_2\times\mathrm{GL}_3$ in the even principal case with Levi sign opposite to $b$ and weight $k_0=0$: for the explicit section built from a determinant power, a block quadratic factor, a squared column-harmonic factor and the standard Gaussian, it identifies both the unfolded torus integral and its dual with the expected products of $\Gamma_{\mathbb{R}}$- and $\Gamma_{\mathbb{C}}$-factors, the dual one up to the archimedean root number and the two sign factors. It supplies the archimedean input, for this branch of the case distinction, to the converse-theorem step used in the Langlands–Tunnell argument, and is cited by [`LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_not_weightOne`](thm.html#LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_not_weightOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3.lean

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

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.Converse
open LanglandsTunnell
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3
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
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ 2) * gaussian3 M) :
        ∃ (σa : ℝ) (e : ℂ), e ≠ 0 ∧
        (∀ s : ℂ, σa < s.re →
            (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr b default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
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
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA b (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = ((archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val * (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card) * e) * (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
                    (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod)) := by sorry
