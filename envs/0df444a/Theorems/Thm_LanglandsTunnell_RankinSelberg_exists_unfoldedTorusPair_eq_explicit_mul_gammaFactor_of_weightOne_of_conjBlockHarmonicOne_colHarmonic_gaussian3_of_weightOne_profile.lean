-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_weightOne_profile
-- name    : LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_weightOne_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/1f10f05b-a443-5e62-a475-2e45290dafec
-- title:
--   Weight-one unfolded torus pair as explicit Γ-factor product
-- statement:
--   Throughout, $K$ is a number field with $[K:\mathbb Q]=3$, whose ring of integers is an integral $\mathcal O_{\mathbb Q}$-algebra, and the measurable-space and Borel instances on $\mathbb A_{\mathbb Q,\infty}=\mathrm{InfiniteAdeleRing}\ \mathbb Q$ and on its unit group, together with the adelic Borel structure on the general linear groups, are the standing instances.
--
--   **Twist data.** $\mu\colon(\mathbb A_K)^\times\to\mathbb C^\times$ is an admissible twist, i.e. `IsAdmissibleTwist K μ`: $\mu$ is trivial on $K^\times$, continuous, and of absolute value $1$ everywhere. The hypothesis `_hns` states that $\mu$ admits no such descent to $\mathbb Q$: there is no admissible twist $\eta$ of $(\mathbb A_{\mathbb Q})^\times$ with $\mu(\varpi_{\mathfrak P})=\eta(\varpi_{\mathfrak p})^{f(\mathfrak P/\mathfrak p)}$ for all primes $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and whose underlying prime $\mathfrak p=\mathfrak P\cap\mathcal O_{\mathbb Q}$ is unramified for $\eta$, where $\varpi$ denotes the uniformiser idele `uniformizerIdele` and $f$ the inertia degree `inertiaDeg'`; here unramifiedness of a character at a finite place means that its local component is trivial on the units of the local integers.
--
--   **Archimedean components of $\mu$.** Functions $u_{\mathbb R},a_{\mathbb R}$ on the real places (values in $\mathbb C$ and $\mathbb Z/2$) and $u_{\mathbb C},k_{\mathbb C}$ on the complex places (values in $\mathbb C$ and $\mathbb Z$) are given, and `huR`, `huC` assert `IsArchCompAt K μ w (uR w) ((aR w).val)` resp. `IsArchCompAt K μ w (uC w) (kC w)`, i.e. the local component of $\mu$ at $w$ sends $x$ to $\|x\|^{\mathrm{mult}(w)\,u}\,(x/\|x\|)^{a}$ with the indicated exponents.
--
--   **The character $\omega$ on $\mathbb Q$.** The hypothesis `hω` has three clauses: $\omega$ is an admissible twist of $(\mathbb A_{\mathbb Q})^\times$; at every prime $p$ of $\mathcal O_{\mathbb Q}$ which is not a bad place for $(K,\mu)$ (that is, $p$ is unramified in $K$ and $\mu$ is unramified at every prime of $K$ above $p$), $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals $\mathrm{inducedE3}$ of the coefficient family $\mathfrak P\mapsto\mu(\varpi_{\mathfrak P})$ (zero at ramified $\mathfrak P$), namely minus the degree-$3$ coefficient of the induced Euler polynomial; and, for every choice of archimedean data $u_{\mathbb R},a_{\mathbb R},u_{\mathbb C},k_{\mathbb C}$ satisfying the two `IsArchCompAt` conditions above and every real place $v$ of $\mathbb Q$, the archimedean component of $\omega$ at $v$ has exponent $\sum_{w\ \mathrm{real}}u_{\mathbb R}(w)+\sum_{w\ \mathrm{complex}}2u_{\mathbb C}(w)$ and integer parameter $\sum_{w\ \mathrm{real}}(a_{\mathbb R}(w))^{\mathrm{val}}+\sum_{w\ \mathrm{complex}}(k_{\mathbb C}(w)+1)$ (finitary sums).
--
--   **Splitting at infinity and additive data.** $E\colon(\mathbb A_{\mathbb Q,\infty})^\times\to(\mathbb A_{\mathbb Q})^\times$ satisfies, by `hE`, that the infinite part of $E(u)$ is $u$ and the finite part of $E(u)$ is $1$. Further, $a\in\mathbb Q$ with $a\neq0$ and $a=-1$; $a_\infty$ is a unit of $\mathbb A_{\mathbb Q,\infty}$ whose underlying element is the image of $a$; and $\psi_\infty$ is the additive character $x\mapsto\psi_{\mathrm{arch}}(a\,x)$, where $\psi_{\mathrm{arch}}$ is the standard archimedean character [`NumberField.StandardAddChar.psiArch`](def/NumberField_StandardGlobalAddCharRat.html#L556).
--
--   **Measures.** $\nu_{\mathrm{add}}$ is the measure $|a|^{1/2}$ times the push-forward of Lebesgue measure under the inverse of the ring equivalence of $\mathbb A_{\mathbb Q,\infty}$ with the mixed space, and $\nu_{\mathrm{mul}}$ is a Haar measure on $(\mathbb A_{\mathbb Q,\infty})^\times$.
--
--   **The $GL_2(\mathbb R)$ parameter and its Whittaker data.** $P$ is a real archimedean parameter (`RealArchParam`: either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb C$, $a_i\in\mathbb Z/2$, or $\mathrm{discrete}(u,k)$ with $k\geq1$), and `_hP₁` requires $|\mathrm{Re}(u_1-u_2)|<1$ in the principal case. Data $k_w\colon\mathbb Z/2\times\{\text{places of }\mathbb Q\}\to\mathbb Z$, $W_r\colon\mathbb Z/2\times\{\text{places}\}\times\mathbb R\to\mathbb C$ and $W_A\colon\mathbb Z/2\times GL_2(\mathbb R)\to\mathbb C$ are subject to nine clauses, each quantified over the parity $\mathrm{par}\in\mathbb Z/2$: `hkw1` and `hkw2` fix the weight, $k_w(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ (as a complex number) at real places $w$ when $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$, and $k_w(\mathrm{par},w)=n+1$ when $P=\mathrm{discrete}(u_0,n)$, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$; `hWr1` says that if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1$ then $W_r(\mathrm{par},w,-t)=(-1)^{a_1^{\mathrm{val}}}W_r(\mathrm{par},w,t)$; `hWr2` says that in the discrete case $W_r(\mathrm{par},w,t)=0$ for $t<0$; `hWr3` says that if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1+1$ then for $\mathrm{Re}\,s$ large the Mellin transform of $t\mapsto(W_r(\mathrm{par},w,t)+(-1)^{a_1^{\mathrm{val}}}W_r(\mathrm{par},w,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}\,(P.\mathrm{twist}\,0\,a_1).\mathrm{archFactor}(s)$; `hWr4` says that for $b=\mathrm{par}$ or $b=\mathrm{par}+P.\mathrm{centralSign}$ the same Mellin transform, taken with the sign $(-1)^{b^{\mathrm{val}}}$, converges for $\mathrm{Re}\,s$ large and equals $(P.\mathrm{twist}\,0\,b).\mathrm{archFactor}(s)$ (the archimedean factor being the product of $\Gamma_{\mathbb R}(s+\mu)$ over the $\mathrm{gammaR}$-multiset times the product of $\Gamma_{\mathbb C}(s+\nu)$ over the $\mathrm{gammaC}$-multiset of the twisted parameter); `hWAN`, `hWAZ`, `hWAK`, `hWAt`, `hWAc` make $W_A(\mathrm{par},\cdot)$ a continuous function on $GL_2(\mathbb R)$ with $W_A(\mathrm{par},u(x)h)=e^{-2\pi i a x}W_A(\mathrm{par},h)$ for the unipotent $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, with central behaviour $W_A(\mathrm{par},zh)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}^{\mathrm{val}}}W_A(\mathrm{par},h)$ for $z\in\mathbb R^\times$, with right equivariance $W_A(\mathrm{par},h\kappa)=\mathrm{archWeightChar}_{\mathbb R}(k_w(\mathrm{par},\mathrm{default}))(\kappa)\,W_A(\mathrm{par},h)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`, and with $W_A(\mathrm{par},\mathrm{diag}(t,1))=W_r(\mathrm{par},\mathrm{default},t)$. Finally $w_{0R}\in GL_2(\mathbb R)$ is the element with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   **The distinguished place and the Levi parameter.** $w_0$ is a real place of $K$, and $P_2$ is a real archimedean parameter for which `hP₂` offers two branches: either $K$ has exactly the three real places $w_0,w_1,w_2$ (pairwise distinct and exhausting the infinite places) and $P_2=\mathrm{principal}(u_{\mathbb R}(w_1),a_{\mathbb R}(w_1),u_{\mathbb R}(w_2),a_{\mathbb R}(w_2))$; or the infinite places of $K$ are exactly one complex place $w_C$ and $w_0$, and then either $k_{\mathbb C}(w_C)\neq0$ and $P_2=\mathrm{discrete}(u_{\mathbb C}(w_C),|k_{\mathbb C}(w_C)|)$, or $k_{\mathbb C}(w_C)=0$ and $P_2=\mathrm{principal}(u_{\mathbb C}(w_C),0,u_{\mathbb C}(w_C),1)$.
--
--   **The Levi datum.** $D$ is an `ArchDatumR P₂`: a function $D.W$ on $2\times2$ real matrices, smooth on the locus of non-vanishing determinant, with the unipotent law $D.W(u(x)g)=\psi(x)D.W(g)$, the central law $D.W(zg)=\mathrm{centralChar}_{P_2}(z)|z|\,D.W(g)$ for $z\neq0$, and a family of entire zeta functions: the zeta integrals $\int W(\mathrm{diag}(y,1)g)\,\mathrm{quasiChar}(u,a)(y)|y|^{s-1}\,d^\times y$ converge in a right half-plane and equal $(P_2.\mathrm{twist}\,u\,a).\mathrm{archFactor}(s)$ times an entire function satisfying the functional equation with $\varepsilon$-factor $(P_2.\mathrm{twist}\,u\,a).\mathrm{epsilonFactor}$ under $g\mapsto wg$, $u\mapsto-(u+P_2.\mathrm{centralExponent})$, $a\mapsto a+P_2.\mathrm{centralSign}$, $s\mapsto1-s$, of finite order in vertical strips, together with the prescribed decay of derivatives at large and small $|y|$ along the torus times the maximal compact. An integer $k_0$ is given with `hDW`: $D.W(x r)=\mathrm{archWeightChar}_{\mathbb R}(k_0)(r)\,D.W(x)$ for $r$ in `rowIsometrySubgroup₀ ℝ`; `hDE`: $D$ is a Casimir eigenvector, $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all invertible $x$; `hDnz`: $D.W$ does not vanish identically; `hk₀min`: in the principal case $P_2=\mathrm{principal}(u_1,a_1,u_2,a_2)$ one has $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, and in the discrete case $P_2=\mathrm{discrete}(u,m)$ one has $k_0=m+1$.
--
--   **Weight-one pins and the section.** `hPw1` requires $P$ to be of principal type with distinct parities; $1\leq k_0$; $n\in\mathbb N$ with $n=k_0-1$; $\mathrm{par}_0\in\mathbb Z/2$; and $S$ is the conjugate-block Gaussian section on $2\times3$ real matrices,
--   $$S(M)=\bigl((M_{00}-iM_{10})-i(M_{01}-iM_{11})\bigr)\,(M_{02}-iM_{12})^{n}\,e^{-\pi\sum_{i,b}M_{ib}^{2}} .$$
--   The Levi branch is pinned by $k_0=1$, $n=0$, and $P_2=\mathrm{principal}(u_1,c_1,u_2,c_2)$ with $c_1\neq c_2$ (these $u_1,u_2,c_1,c_2$ being fresh parameters of $P_2$, not those of $P$). Lastly $\rho\in\mathbb C$ is a scalar for which `hρ` holds: for every $b\in\mathbb Z/2$ and every $\tau>0$,
--   $$D.W(\mathrm{diag}(\tau,1))+(-1)^{b^{\mathrm{val}}}D.W(\mathrm{diag}(-\tau,1))=\rho\,\tau\cdot 4\int_{0}^{\infty}r^{\,u_1+\mathrm{signShift}(c_1+b)}e^{-\pi r^{2}}\,(\tau/r)^{\,u_2+\mathrm{signShift}(c_2+b)}e^{-\pi(\tau/r)^{2}}\,\frac{dr}{r}.$$
--
--   **Conclusion.** There exists $\sigma_1\in\mathbb R$ such that for every $s\in\mathbb C$ with $\sigma_1<\mathrm{Re}\,s$,
--   $$\int_{e}\mathrm{quasiChar}\bigl(u_{\mathbb R}(w_0)+2,\;a_{\mathbb R}(w_0)\bigr)(\det e)\;|\det e|^{-2}\,\Bigl(\int_{\mathbb R}W_r(\mathrm{par}_0,\mathrm{default},t)\,D.W\bigl(\mathrm{diag}(at,1)\,e^{-1}\bigr)\,|t|^{\,s-1/2}\,\frac{dt}{t^{2}}\Bigr)\Bigl(\int_{0}^{\infty}y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\,\mathrm{godementInner3}\bigl(\psi_\infty\text{ shifted by }\mathrm{ofReal}(y)\bigr)\,S\,(e)\,1\;dy\Bigr)\,de$$
--   $$=\Bigl((-1)^{a_{\mathbb R}(w_0)^{\mathrm{val}}+1}\frac{\pi}{2}\Bigr)\rho\;\cdot\;\prod_{x\in\Gamma_{\mathbb R}\text{-multiset}}\Gamma_{\mathbb R}\bigl(s+\tfrac12+x\bigr)\;\prod_{x\in\Gamma_{\mathbb C}\text{-multiset}}\Gamma_{\mathbb C}\bigl(s+\tfrac12+x\bigr),$$
--   where the outer integral is over all $2\times2$ real matrices $e$ (as functions $\mathrm{Fin}\,2\to\mathrm{Fin}\,2\to\mathbb R$ with Lebesgue measure), $\mathrm{quasiChar}(u,a)(y)=|y|^{u}$ times $1$ or $\mathrm{sign}(y)$ according as $a=0$ or $a\neq0$, $\mathrm{ofReal}(y)$ is the infinite adele with component $y$ at each place, and
--   $$\mathrm{godementInner3}(\psi,S,h,m)=\int_{v\in\mathbb R^{2}}S\Bigl(h\cdot\begin{pmatrix}m_{0b}+v_0m_{2b}\\ m_{1b}+v_1m_{2b}\end{pmatrix}_{b}\Bigr)\,\psi\bigl(\mathrm{ofReal}(-v_1)\bigr)\,dv ,$$
--   evaluated at $h=e$ and $m$ the identity $3\times3$ matrix. The two multisets are $\mathrm{twistedGammaR}\,K\,(\mathrm{archOfParamR}\,K\,P)\,u_{\mathbb R}\,a_{\mathbb R}$ and $\mathrm{twistedGammaC}\,K\,(\mathrm{archOfParamR}\,K\,P)\,(\mathrm{archOfParamC}\,K\,P)\,u_{\mathbb R}\,a_{\mathbb R}\,u_{\mathbb C}\,k_{\mathbb C}$: with the constant assignments $\mathrm{archOfParamR}$, $\mathrm{archOfParamC}$ (the same $P$ at each real place, its base change $\mathrm{principal}(\tilde u_1,\tilde a_1,\tilde u_2,\tilde a_2)\mapsto\langle\tilde u_1,0,\tilde u_2,0\rangle$ at each complex place), the first is the multiset sum over the real places $w$ of the $\mathrm{gammaR}$-multiset of $P$ twisted by $(u_{\mathbb R}(w),a_{\mathbb R}(w))$, and the second is the sum of the $\mathrm{gammaC}$-multisets of those twisted real-place parameters (empty since $P$ is of principal type) and of the $\mathrm{gammaC}$-multisets of the base-changed parameter twisted by $(u_{\mathbb C}(w),k_{\mathbb C}(w))$ over the complex places $w$.
--
--   This is the archimedean Rankin–Selberg computation on the weight-one principal Levi branch of the cubic induction: after unfolding, the archimedean zeta integral of the conjugate-block Gaussian Godement section against the torus Whittaker function of the Levi datum $D$ is evaluated in closed form as $(-1)^{a_0+1}(\pi/2)\rho$ times the $\Gamma_{\mathbb R}$- and $\Gamma_{\mathbb C}$-products predicted for the induced parameter, the constant being explicit. It feeds the combined primal/dual statement [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3), which supplies the archimedean input to the converse theorem used in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_weightOne_profile.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_weightOne_profile
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
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (hk1 : k₀ = 1) (hn0 : n = 0)
    (u₁ u₂ : ℂ) (c₁ c₂ : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c₁ u₂ c₂) (hc : c₁ ≠ c₂)
    (ρ : ℂ)
    (hρ : ∀ (b : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁ + signShift (c₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (u₂ + signShift (c₂ + b)) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ))) :
    ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
            (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
              = (((-1 : ℂ) ^ ((aR w₀ h₀).val + 1) * ((Real.pi : ℂ) / 2)) * ρ) * (((twistedGammaR K (archOfParamR K P) uR aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod) := by sorry
