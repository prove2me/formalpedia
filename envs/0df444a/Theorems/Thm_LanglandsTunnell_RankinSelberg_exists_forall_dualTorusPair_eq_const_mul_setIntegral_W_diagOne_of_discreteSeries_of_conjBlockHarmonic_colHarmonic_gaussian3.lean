-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/310bacb4-e931-5b77-811c-867899b5ac35
-- title:
--   Dual torus pair for a discrete-series profile: Gamma factors times Laplace–Mellin
-- statement:
--   Setting and data. $K$ is a field of characteristic zero which is a number field, equipped with an algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$ that is integral, and with $[K:\mathbb{Q}]=3$ (hypothesis `_hdeg`). The character $\mu$ is a monoid homomorphism from the ideles $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ which is an admissible twist (`_hμ`), i.e. trivial on the image of $K^\times$, continuous, and of absolute value $1$ at every idele. The hypothesis `_hns` asserts that $\mu$ is not obtained from $\mathbb{Q}$ in the following sense: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified (its local component is trivial on the units of the valuation ring) and whose prime $p=\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ has $\eta$ unramified, $\mu$ of the uniformiser idele at $\mathfrak{P}$ equals $\eta$ of the uniformiser idele at $p$ raised to the inertia degree `inertiaDeg'` of $\mathfrak{P}$ over $p$.
--
--   Archimedean parameters of $\mu$. Functions $uR, aR$ on the real places and $uC, kC$ on the complex places of $K$ record, via `huR` and `huC`, that at each real place $w$ the archimedean local component of $\mu$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,uR(w)}\,(\sigma_w(x)/\|x\|)^{(aR(w)).\mathrm{val}}$, and at each complex place $w$ it is $x\mapsto\|x\|^{\mathrm{mult}(w)\,uC(w)}(\sigma_w(x)/\|x\|)^{kC(w)}$, where $\sigma_w$ is the embedding of the completion.
--
--   The character $\omega$ of $\mathbb{Q}$. The hypothesis `hω` has three clauses: $\omega$ is an admissible twist of $\mathbb{Q}$; at every prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ which is not a bad place for $(K,\mu)$ (that is, $p$ is unramified in $K$ — no prime of the fibre has ramification index $\neq 1$ — and $\mu$ is unramified at every prime above $p$), $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\text{uniformiser idele at }p)$ equals `inducedE3 ℚ (inducedCoeff K μ) p`, the negative of the degree-$3$ coefficient of the induced Euler polynomial formed from the coefficients $\mathfrak{P}\mapsto\mu(\text{uniformiser idele at }\mathfrak{P})$ (set to $0$ at ramified $\mathfrak{P}$); and, for any archimedean data $uR,aR,uC,kC$ satisfying the two `IsArchCompAt` conditions above, at every real place $v$ of $\mathbb{Q}$ the archimedean component of $\omega$ at $v$ has exponent $\sum_{w\ \mathrm{real}} uR(w)+\sum_{w\ \mathrm{complex}} 2\,uC(w)$ and integer parameter $\sum_{w\ \mathrm{real}}(aR(w)).\mathrm{val}+\sum_{w\ \mathrm{complex}}(kC(w)+1)$ (finite sums).
--
--   Adelic normalisations. $E$ is a homomorphism from the units of the infinite adeles of $\mathbb{Q}$ to the ideles of $\mathbb{Q}$ splitting the infinite part: `hE` says that the infinite part of $E(u)$ is $u$ and its finite part is $1$. The rational number $a$ is non-zero and equal to $-1$ (`ha`, `ha1`); $a_{\infty}$ is an infinite-adelic unit with underlying element $\iota(a)$ (`haInf`); $\psi_\infty$ is the additive character $x\mapsto\psi_{\mathrm{arch}}(a x)$ built from the standard archimedean character (`hpsiInf`). Measurable-space and Borel-space structures on the infinite adeles and on their unit group are assumed; $\nu_{\mathrm{add}}$ is the measure $\mathrm{ofReal}(|a|^{1/2})$ times the pushforward of Lebesgue measure under the inverse of the identification `InfiniteAdeleRing.ringEquiv_mixedSpace ℚ` (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on the unit group.
--
--   The $GL_2$ archimedean profile. $P$ is a real archimedean parameter (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb{C}$, $a_i\in\mathbb{Z}/2$, or $\mathrm{discrete}(u,k)$ with $k\geq 1$); `_hP₁` requires that in the principal case $|\mathrm{Re}(u_1-u_2)|<1$. Data $kw:\mathbb{Z}/2\times\{\text{places of }\mathbb{Q}\}\to\mathbb{Z}$, $Wr:\mathbb{Z}/2\times\{\text{places}\}\to(\mathbb{R}\to\mathbb{C})$ and $WA:\mathbb{Z}/2\to(GL_2(\mathbb{R})\to\mathbb{C})$ are subject to: `hkw1`, in the principal case $kw(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ (where $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$); `hkw2`, in the discrete case of weight $n$, $kw(\mathrm{par},w)=n+1$; `hWr1`, if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1$ then $Wr(\mathrm{par},w)(-t)=(-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w)(t)$; `hWr2`, in the discrete case $Wr(\mathrm{par},w)(t)=0$ for $t<0$; `hWr3`, if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1+1$ then for $\mathrm{Re}\,s$ beyond some abscissa the Mellin transform of $t\mapsto (Wr(\mathrm{par},w)(t)+(-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w)(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}\,0\,a_1$ at $s$; `hWr4`, for each $\mathrm{par}$ and each $b$ with $b=\mathrm{par}$ or $b=\mathrm{par}+P.\mathrm{centralSign}$, the analogous Mellin transform with $(-1)^{b.\mathrm{val}}$ converges for $\mathrm{Re}\,s$ large and equals the archimedean factor of $P.\mathrm{twist}\,0\,b$ at $s$. The function $WA$ satisfies the Whittaker laws: `hWAN`, $WA(\mathrm{par})\big(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\big)h)=e^{-2\pi i a x}\,WA(\mathrm{par})(h)$; `hWAZ`, $WA(\mathrm{par})(z\cdot h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}\,WA(\mathrm{par})(h)$ for scalar matrices $z$; `hWAK`, $WA(\mathrm{par})(h\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(kw(\mathrm{par},\mathrm{default}))(\kappa)\,WA(\mathrm{par})(h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt`, $WA(\mathrm{par})(\mathrm{diag}(t,1))=Wr(\mathrm{par},\mathrm{default})(t)$ for $t\in\mathbb{R}^\times$; and `hWAc`, continuity of each $WA(\mathrm{par})$. The element $w_{0R}\in GL_2(\mathbb{R})$ is the matrix $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ (`hw₀R`).
--
--   The Levi datum. $w_0$ is a real place of $K$. The parameter $P_2$ satisfies the disjunction `hP₂`: either $K$ has exactly the three pairwise distinct real places $w_0,w_1,w_2$ and $P_2=\mathrm{principal}(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$; or $K$ has a complex place $w_C$ and the places of $K$ are exactly $w_C$ and $w_0$, and either $kC(w_C)\neq 0$ and $P_2=\mathrm{discrete}(uC(w_C),|kC(w_C)|)$, or $kC(w_C)=0$ and $P_2=\mathrm{principal}(uC(w_C),0,uC(w_C),1)$. $D$ is an archimedean Whittaker datum of type $P_2$ (a function $D.W$ on $2\times 2$ real matrices, smooth on the invertible locus, with the unipotent and central transformation laws, together with an entire zeta function, its integral representation, functional equation, finite order and decay estimates), and $k_0\in\mathbb{Z}$ is an integer such that: `hDW`, $D.W(x\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(\kappa)\,D.W(x)$ for $\kappa\in$ `rowIsometrySubgroup₀ ℝ`; `hDE`, $D$ is a Casimir eigenvector, $-\big(\tfrac14 H^2-\tfrac12 H+EF\big)D.W=P_2.\mathrm{laplaceEigenvalue}\cdot D.W$ on invertible matrices; `hDnz`, $D.W$ does not vanish identically; and `hk₀min`, in the principal case $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2 \bmod 2$, and in the discrete case of weight $m'$, $k_0=m'+1$.
--
--   The discrete-series specialisation. $P=\mathrm{discrete}(u_P,n_P)$ with $n_P\geq 1$ (`hPdisc`), $m=n_P+1$ (`hm`), and $n\in\mathbb{N}$, $\varepsilon'\in\mathbb{R}$ satisfy `hcol`: either $\varepsilon'=-1$ and $n=k_0-m$, or $\varepsilon'=1$ and $n=m-k_0$. A parity $\mathrm{par}_0\in\mathbb{Z}/2$ is fixed. The Schwartz datum $S$ on $2\times 3$ real matrices is given explicitly (`hS`) by
--   $$S(M)=\big((M_{00}-iM_{10})-i(M_{01}-iM_{11})\big)^m\,(M_{02}+\varepsilon' i M_{12})^n\,\exp\!\big(-\pi\textstyle\sum_{i,b}M_{ib}^2\big).$$
--   Finally, the one-sided profile is prescribed: $Wr(\mathrm{par}_0,\mathrm{default})(t)=2\,t^{u_P+n_P/2+1}e^{-2\pi t}$ for $t>0$ (`hWpos`) and $=0$ for $t<0$ (`hWneg`).
--
--   Conclusion. There exists $\sigma_a\in\mathbb{R}$ such that for every $s\in\mathbb{C}$ with $\sigma_a<\mathrm{Re}\,s$,
--   $$\int_{a_2\in(0,\infty)}\int_{a_1\in\mathbb{R}} F_s(a_1,a_2)\,da_1\,da_2 = R(s),$$
--   where the inner integrand $F_s(a_1,a_2)$ is $0$ unless $a_1\neq 0$ and $a_2>0$, and in that case, writing $q=\left(\begin{smallmatrix}a_1&0\\0&a_2\end{smallmatrix}\right)\in GL_2(\mathbb{R})$,
--   $$F_s(a_1,a_2)=|\det q|\;WA(\mathrm{par}_0)\big(w_{0R}\,{}^t q^{-1}\big)\cdot \Lambda\big(\mathrm{longWeyl}_3\cdot {}^t(\cdot)^{-1}\text{ of the archimedean component of }\iota(q)\big)\cdot |\det q|^{\,s-1/2}\cdot a_1^{-2}.$$
--   Here ${}^tq^{-1}$ is [`RSCarrier.transposeInv q`](def/LanglandsTunnell_RSCarrier.html#L31); $\iota(q)$ is the image of $q$ under the real-place inclusion $GL_2(\mathbb{R})\to GL_2(\mathbb{A}_{\mathbb{Q}})$ at the (unique real) place of $\mathbb{Q}$ followed by the block embedding into $GL_3(\mathbb{A}_{\mathbb{Q}})$, and its archimedean component is taken in $GL_3$ of the infinite adeles; $\Lambda$ is the Jacquet vector `jacquetVector3 D (uR w₀) (aR w₀) a psiInf S`, namely $g\mapsto \mathrm{quasiChar}(uR(w_0)+1)(aR(w_0))(\det\text{ of the real matrix of }g)\cdot\int_{e:\,2\times 2\text{ real}}\mathrm{jacquetIntegrand3}\,D\,(uR(w_0))\,(aR(w_0))\,a\,\psi_\infty\,S\,g\,e$, and the dual Whittaker function $\mathrm{dualWhittakerFn3}\,\Lambda$ evaluates $\Lambda$ at $\mathrm{longWeyl}_3\cdot{}^tg^{-1}$ with $\mathrm{longWeyl}_3$ the matrix with $1$ in positions $(0,2),(1,1),(2,0)$ and $0$ elsewhere.
--
--   The right-hand side is
--   $$R(s)=\pi\, i^{m}\,(-1)^{m+n+(aR(w_0)).\mathrm{val}}\,2^{m}\;\Gamma_{\mathbb{R}}\big(2s-P.\mathrm{centralExponent}-P_2.\mathrm{centralExponent}+n+1\big)$$
--   $$\times\,(2\pi)^{-(s-uR(w_0)-u_P+m/2)}\;\Gamma\big(s-uR(w_0)-u_P+m/2\big)\;\int_0^{\infty} D.W\big(\mathrm{diag}(v,1)\big)\,v^{\,s-u_P-P_2.\mathrm{centralExponent}+m/2-2}\,e^{-2\pi v}\,dv,$$
--   where $P.\mathrm{centralExponent}=2u_P$ in the discrete case and $\mathrm{diag}(v,1)$ is the matrix $\left(\begin{smallmatrix}v&0\\0&1\end{smallmatrix}\right)$.
--
--   This is the Levi-generic evaluation of the dual branch of the unfolded Rankin–Selberg torus-pair integral for the $GL_3\times GL_2$ pair attached to a cubic field and an idele class character, in the case of a discrete-series archimedean $GL_2$ profile and the explicit degree-$(m,n)$ harmonic flat section against the Gaussian: the whole archimedean double integral collapses to a product of $\Gamma$-factors times the Laplace–Mellin transform $\int_0^\infty D.W(\mathrm{diag}(v,1))v^{Z-2}e^{-2\pi v}\,dv$ of the positive torus sheet of the Levi datum. It is cited by the three branch results that specialise the Levi datum to weight zero, weight one and the discrete series, each of which evaluates that remaining transform in closed form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3.lean

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
open LanglandsTunnell.CubicInduction
open LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
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
    (hWneg : ∀ t : ℝ, t < 0 → Wr par₀ default t = 0) :
    ∃ σa : ℝ, ∀ s : ℂ, σa < s.re →
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = (Real.pi : ℂ) * Complex.I ^ m * (-1 : ℂ) ^ (m + n + (aR w₀ h₀).val) * (2 : ℂ) ^ m *
              Complex.Gammaℝ (2 * s - P.centralExponent - P₂.centralExponent + (n : ℂ) + 1) *
              (2 * (Real.pi : ℂ)) ^ (-(s - uR w₀ h₀ - uP + (m : ℂ) / 2)) * Complex.Gamma (s - uR w₀ h₀ - uP + (m : ℂ) / 2) *
              (∫ v in Set.Ioi (0 : ℝ), D.W (ArchR.diagOne v) * ((v : ℝ) : ℂ) ^ (s - uP - P₂.centralExponent + (m : ℂ) / 2 - 2) *
                (Real.exp (-(2 * Real.pi * v)) : ℂ)) := by sorry
