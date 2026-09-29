-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_weightOneLevi_ed2
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_weightOneLevi_ed2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/58008629-59b2-50b3-b47c-5ef5f5640723
-- title:
--   Unfolded torus pair in closed form: discrete series against principal Levi
-- statement:
--   Throughout, $K$ is a number field of degree $3$ over $\mathbb{Q}$ (hypothesis `_hdeg`), equipped with an integral algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$.
--
--   **Global frame (the data carried from the unfolding step).** $\mu\colon(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ is a monoid homomorphism which is an *admissible twist* (`_hμ`): trivial on the image of $K^\times$, continuous, and of absolute value $1$ everywhere. The hypothesis `_hns` states that $\mu$ is not induced from $\mathbb{Q}$ in the following sense: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose contraction $p=\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ is unramified for $\eta$, one has $\mu(\varpi_{\mathfrak{P}})=\eta(\varpi_{p})^{f}$ with $f$ the inertia degree of $\mathfrak{P}$ over $p$; here unramifiedness of a character at a finite place means that its local component is trivial on the units of the local integers, and $\varpi$ denotes the idele with uniformizer entry at the given place. The functions $u_R,a_R$ (on real places of $K$, with values in $\mathbb{C}$ and $\mathbb{Z}/2$) and $u_C,k_C$ (on complex places, with values in $\mathbb{C}$ and $\mathbb{Z}$) record the archimedean components of $\mu$ in the sense of `IsArchCompAt` (`huR`, `huC`): at a place $w$ the local character of $\mu$ on $(K_w)^\times$ is $x\mapsto\|x\|^{\operatorname{mult}(w)\,u}\,(x/\|x\|)^{a}$, with $(u,a)=(u_R(w),a_R(w)^{\mathrm{val}})$ at real places and $(u_C(w),k_C(w))$ at complex places. Further, $\omega\colon(\mathbb{A}_{\mathbb{Q}})^\times\to\mathbb{C}^\times$ satisfies the three clauses of `hω`: $\omega$ is an admissible twist of $\mathbb{Q}$; at every finite place $p$ of $\mathbb{Q}$ which is not bad for $(K,\mu)$ — bad meaning that $p$ ramifies in $K$ or that $\mu$ is ramified at some prime of the fibre over $p$ — the character $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals $\operatorname{inducedE3}$ of the family $\mathfrak{P}\mapsto\mu(\varpi_{\mathfrak{P}})$ (the negative of the degree-$3$ coefficient of the induced Euler polynomial) at $p$; and, for any archimedean data $(u_R,a_R,u_C,k_C)$ of $\mu$ as above and any real place $v$ of $\mathbb{Q}$, the archimedean component of $\omega$ at $v$ has exponent $\sum_{w\ \mathrm{real}}u_R(w)+\sum_{w\ \mathrm{cplx}}2u_C(w)$ and integer $\sum_{w\ \mathrm{real}}a_R(w)^{\mathrm{val}}+\sum_{w\ \mathrm{cplx}}(k_C(w)+1)$ (the sums being finite sums over the respective sets of places). Finally $E$ is a homomorphism from the infinite idele units of $\mathbb{Q}$ to the full idele units splitting the infinite part (`hE`: infinite part of $E(u)$ is $u$, finite part is $1$); $a\in\mathbb{Q}$ is nonzero and equal to $-1$ (`ha`, `ha1`), `aInf` is an infinite idele unit whose underlying adele is the image of $a$ (`haInf`); `psiInf` is the additive character $x\mapsto\psi_{\mathrm{arch}}(a x)$ on the infinite adeles (`hpsiInf`); and the measure normalisations are $\nu_{\mathrm{add}}=|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the mixed-space ring equivalence (`hν_add`) and $\nu_{\mathrm{mul}}$ a Haar measure on the infinite idele units.
--
--   **The $\mathbb{Q}$-side archimedean profile.** $P$ is a real archimedean parameter (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb{C}$, $a_i\in\mathbb{Z}/2$, or $\mathrm{discrete}(u,k)$ with $k\ge1$), subject to `_hP₁`: in the principal case $|\Re(u_1-u_2)|<1$. The weights $kw\colon\mathbb{Z}/2\times\{\text{places of }\mathbb{Q}\}\to\mathbb{Z}$, the torus profiles $Wr(\mathrm{par},w,\cdot)\colon\mathbb{R}\to\mathbb{C}$ and the group functions $WA(\mathrm{par},\cdot)\colon GL_2(\mathbb{R})\to\mathbb{C}$ are constrained as follows. Weights: at a real place, $kw(\mathrm{par},w)=\operatorname{signShift}(a_1+\mathrm{par})+\operatorname{signShift}(a_2+\mathrm{par})$ when $P$ is principal (`hkw1`, with $\operatorname{signShift}(0)=0$, $\operatorname{signShift}(1)=1$), and $kw(\mathrm{par},w)=k+1$ when $P=\mathrm{discrete}(u,k)$ (`hkw2`). Profiles: if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ (equal parities) and $\mathrm{par}=a_1$ then $Wr(\mathrm{par},w,-t)=(-1)^{a_1^{\mathrm{val}}}Wr(\mathrm{par},w,t)$ (`hWr1`); if $P$ is discrete then $Wr(\mathrm{par},w,t)=0$ for $t<0$ (`hWr2`); if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1+1$ then for $\Re s$ large the Mellin transform of $t\mapsto\bigl(Wr(\mathrm{par},w,t)+(-1)^{a_1^{\mathrm{val}}}Wr(\mathrm{par},w,-t)\bigr)/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P$ twisted by $(0,a_1)$ (`hWr3`); and for every $b$ with $b=\mathrm{par}$ or $b=\mathrm{par}+P.\mathrm{centralSign}$, for $\Re s$ large the same Mellin transform (with $b$ in place of $a_1$) converges and equals the archimedean factor of $P$ twisted by $(0,b)$ (`hWr4`). Here the archimedean factor of a parameter is the product of $\Gamma_{\mathbb{R}}(s+u_i+\operatorname{signShift}a_i)$ in the principal case and $\Gamma_{\mathbb{C}}(s+u+k/2)$ in the discrete case, and the central sign is $a_1+a_2$, respectively $k+1$ mod $2$. The functions $WA$ satisfy the Whittaker transformation laws: $WA(\mathrm{par},u(x)h)=e^{-2\pi i a x}WA(\mathrm{par},h)$ for unipotent $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ (`hWAN`); $WA(\mathrm{par},z h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}^{\mathrm{val}}}WA(\mathrm{par},h)$ for scalar matrices $z$ (`hWAZ`); right transformation by the character `archWeightCharℝ` of weight $kw(\mathrm{par},\mathrm{default})$ under the subgroup `rowIsometrySubgroup₀ ℝ` (`hWAK`); $WA(\mathrm{par},\operatorname{diag}(t,1))=Wr(\mathrm{par},\mathrm{default},t)$ (`hWAt`); and continuity in each parity (`hWAc`). Also $w_{0R}\in GL_2(\mathbb{R})$ is the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀R`).
--
--   **The Levi-side archimedean datum.** $w_0$ is a real place of $K$, and $P_2$ is a real archimedean parameter satisfying the dichotomy `hP₂`: either $K$ has exactly three real places $w_0,w_1,w_2$, pairwise distinct and exhausting all infinite places, and $P_2=\mathrm{principal}(u_R(w_1),a_R(w_1),u_R(w_2),a_R(w_2))$; or $K$ has exactly the places $w_0$ and one complex place $w_C$, and either $k_C(w_C)\neq0$ and $P_2=\mathrm{discrete}(u_C(w_C),|k_C(w_C)|)$, or $k_C(w_C)=0$ and $P_2=\mathrm{principal}(u_C(w_C),0,u_C(w_C),1)$. Next, $D$ is an archimedean datum of type $P_2$ (a function $D.W$ on $2\times2$ real matrices, smooth on the invertible locus, with the unipotent law $D.W(u(x)g)=\psi(x)D.W(g)$, the central law $D.W(zg)=\mathrm{centralChar}_{P_2}(z)|z|D.W(g)$, an entire zeta function with prescribed convergence abscissa, the Mellin identity expressing the zeta integral as the archimedean factor of the twisted parameter times the entire zeta, the functional equation with epsilon factor under $g\mapsto w g$ and $(u,a,s)\mapsto(-(u+P_2.\mathrm{centralExponent}),a+P_2.\mathrm{centralSign},1-s)$, finite order in vertical strips, and the decay bounds at infinity and at zero), and $k_0\in\mathbb{Z}$. The conditions on $D$ are: right weight-$k_0$ equivariance $D.W(x r)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(r)\,D.W(x)$ for $r$ in `rowIsometrySubgroup₀ ℝ` (`hDW`); $D$ is a Casimir eigenfunction, i.e. $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all $x$ with $\det x\neq0$ (`hDE`); $D.W$ is not identically zero on $GL_2(\mathbb{R})$ (`hDnz`); and the minimality of $k_0$ (`hk₀min`): in the principal case $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, in the discrete case with weight $m'$ one has $k_0=m'+1$.
--
--   **The branch under consideration.** $P=\mathrm{discrete}(u_P,n_P)$ with $n_P\ge1$ (`hPdisc`) and $m=n_P+1$ (`hm`); the pair $(\varepsilon',n)\in\mathbb{R}\times\mathbb{N}$ satisfies `hcol`: either $\varepsilon'=-1$ and $n=k_0-m$, or $\varepsilon'=1$ and $n=m-k_0$. A parity $\mathrm{par}_0\in\mathbb{Z}/2$ is fixed, and the section $S$ on $2\times3$ real matrices is given (`hS`) by
--   $$S(M)=\bigl((M_{00}-iM_{10})-i(M_{01}-iM_{11})\bigr)^{m}\bigl(M_{02}+\varepsilon' i M_{12}\bigr)^{n}e^{-\pi\sum_{i,b}M_{ib}^2}.$$
--   The profile at the parity $\mathrm{par}_0$ and the place $\mathrm{default}$ of $\mathbb{Q}$ is explicit: $Wr(\mathrm{par}_0,\mathrm{default},t)=2t^{\,u_P+n_P/2+1}e^{-2\pi t}$ for $t>0$ (`hWpos`) and $=0$ for $t<0$ (`hWneg`). On the Levi side, $k_0=1$ (`hk₀`), $P_2=\mathrm{principal}(\mu_1,c_1,\mu_2,c_2)$ with $c_1\neq c_2$ (`hP₂eq`, `hc`), and $\rho\in\mathbb{C}$ is a scalar for which the torus values of $D.W$ are given by a Gaussian convolution (`hD`): for every $b\in\mathbb{Z}/2$ and every $\tau>0$,
--   $$D.W\bigl(\operatorname{diag}(\tau,1)\bigr)+(-1)^{b^{\mathrm{val}}}D.W\bigl(\operatorname{diag}(-\tau,1)\bigr)=\rho\,\tau\cdot 4\int_0^\infty r^{\mu_1+\operatorname{signShift}(c_1+b)}e^{-\pi r^2}\,(\tau/r)^{\mu_2+\operatorname{signShift}(c_2+b)}e^{-\pi(\tau/r)^2}\,\frac{dr}{r},$$
--   where $\operatorname{diag}(y,1)$ denotes the matrix $\begin{pmatrix}y&0\\0&1\end{pmatrix}$.
--
--   **Conclusion.** There exists $\sigma_a\in\mathbb{R}$ such that for every $s\in\mathbb{C}$ with $\sigma_a<\Re s$ the unfolded torus pair, namely the integral over $e\in M_2(\mathbb{R})$ (Lebesgue measure in the four entries) of
--   $$q(\det e)\,|\det e|^{-2}\left(\int_{\mathbb{R}}Wr(\mathrm{par}_0,\mathrm{default},t)\;D.W\bigl(\operatorname{diag}(a t,1)\,e^{-1}\bigr)\,|t|^{\,s-1/2}\,t^{-2}\,dt\right)\left(\int_0^\infty y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\,I(y,e)\,dy\right),$$
--   where $q=\mathrm{quasiChar}(u_R(w_0)+2,a_R(w_0))$, i.e. $q(x)=|x|^{u_R(w_0)+2}$ multiplied by $\operatorname{sign}(x)$ if $a_R(w_0)\neq0$ and by $1$ otherwise, and where
--   $$I(y,e)=\int_{\mathbb{R}^2}S\!\left(e\cdot\begin{pmatrix}1&0&v_0\\0&1&v_1\end{pmatrix}\right)\psi^{(y)}\bigl(\operatorname{ofReal}(-v_1)\bigr)\,dv$$
--   is the Godement inner integral of $S$ at the matrix $e$ and the identity $3\times3$ matrix, taken against the multiplicative shift $\psi^{(y)}$ of `psiInf` by the infinite adele $\operatorname{ofReal}(y)$ with all components equal to $y$, is equal to
--   $$\pi\,\Gamma_{\mathbb{R}}\bigl(P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s+n+1\bigr)(-\varepsilon')^{n}(-1)^{a_R(w_0)^{\mathrm{val}}+m}\,2^{m}\,(2\pi)^{-(s+u_P+u_R(w_0)+m/2)}\,\Gamma\bigl(s+u_P+u_R(w_0)+\tfrac m2\bigr)$$
--   times
--   $$\rho\,\Gamma_{\mathbb{R}}\bigl(2(s+u_P+\tfrac m2)+\mu_1+\mu_2+1\bigr)\Bigl[B\bigl(\sigma+\mu_1+\operatorname{signShift}c_1,\;\sigma+\mu_2+\operatorname{signShift}c_2\bigr)+B\bigl(\sigma+\mu_1+\operatorname{signShift}(c_1+1),\;\sigma+\mu_2+\operatorname{signShift}(c_2+1)\bigr)\Bigr],$$
--   with $\sigma=s+u_P+\tfrac m2$, where $B$ is the Euler beta integral $B(p,q)=\int_0^1t^{p-1}(1-t)^{q-1}dt$ and $\Gamma_{\mathbb{R}}(z)=\pi^{-z/2}\Gamma(z/2)$. In the present branch the central exponents are $P.\mathrm{centralExponent}=2u_P$ and $P_2.\mathrm{centralExponent}=\mu_1+\mu_2$.
--
--   This is the archimedean computation for one branch of the Rankin–Selberg unfolding used in the converse-theorem input to the cubic base change of Langlands and Tunnell: for a discrete-series profile on the $\mathbb{Q}$ side and a principal-series Levi datum of opposite parities with minimal weight $k_0=1$, the unfolded torus pair is evaluated in closed form as a product of gamma factors with a sum of two beta integrals. It is used, together with the corresponding dual computation, by the two assembly statements that identify the archimedean gamma factor in the three-real-places and the one-complex-place cases, and it rests on the general unfolding identity for this configuration together with the evaluation of a Gaussian-convolution Mellin integral as a beta times $\Gamma_{\mathbb{R}}$ factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_weightOneLevi_ed2.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_weightOneLevi_ed2
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
    (hk₀ : k₀ = 1) (μ₁ μ₂ : ℂ) (c₁ c₂ : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal μ₁ c₁ μ₂ c₂) (hc : c₁ ≠ c₂) (ρ : ℂ)
    (hD : ∀ (b : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁ + signShift (c₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂ + signShift (c₂ + b)) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ))) :
    ∃ σa : ℝ, ∀ s : ℂ, σa < s.re →
            (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
              = (Real.pi : ℂ) * Complex.Gammaℝ (P.centralExponent + P₂.centralExponent + 2 * s + (n : ℂ) + 1) *
              ((-(ε' : ℂ)) ^ n) * (-1 : ℂ) ^ ((aR w₀ h₀).val + m) * (2 : ℂ) ^ m *
              (2 * (Real.pi : ℂ)) ^ (-(s + uP + uR w₀ h₀ + (m : ℂ) / 2)) * Complex.Gamma (s + uP + uR w₀ h₀ + (m : ℂ) / 2) *
              (ρ * Complex.Gammaℝ (2 * (s + uP + (m : ℂ) / 2) + μ₁ + μ₂ + 1) *
                (Complex.betaIntegral (s + uP + (m : ℂ) / 2 + μ₁ + signShift c₁) (s + uP + (m : ℂ) / 2 + μ₂ + signShift c₂) +
                 Complex.betaIntegral (s + uP + (m : ℂ) / 2 + μ₁ + signShift (c₁ + 1)) (s + uP + (m : ℂ) / 2 + μ₂ + signShift (c₂ + 1)))) := by sorry
