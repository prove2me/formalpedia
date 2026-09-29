-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_dualTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_weightOneLevi
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_weightOneLevi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/bd6f1f68-111d-5cd0-9e9e-76ed72becca3
-- title:
--   Closed form of the dual torus pair, weight-one Levi branch
-- statement:
--   Global data. Let $K$ be a number field of degree $3$ over $\mathbb Q$ (hypothesis `_hdeg`), with $\mathcal O_K$ an integral $\mathcal O_{\mathbb Q}$-algebra, and let $\mu\colon(\mathbb A_K)^\times\to\mathbb C^\times$ be an admissible twist, i.e. (`IsAdmissibleTwist`) an idele class character — trivial on the image of $K^\times$ — which is continuous and unitary. The hypothesis `_hns` asserts that $\mu$ does not descend to $\mathbb Q$ in the following sense: there is no admissible twist $\eta$ of $(\mathbb A_{\mathbb Q})^\times$ such that for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and with $\eta$ unramified at the prime $\mathfrak p=\mathfrak P\cap\mathcal O_{\mathbb Q}$ below it, one has $\mu(\varpi_{\mathfrak P})=\eta(\varpi_{\mathfrak p})^{f(\mathfrak P/\mathfrak p)}$, where $\varpi$ denotes the uniformizer idele and $f$ the inertia degree. Families $uR,aR$ (over the real places of $K$) and $uC,kC$ (over the complex places) record the archimedean parameters of $\mu$: by `huR` and `huC`, at each real place $w$ the local component of $\mu$ on $(K_w)^\times$ is $x\mapsto\|x\|^{\mathrm{mult}(w)\,uR_w}\,(x/\|x\|)^{(aR_w).\mathrm{val}}$, and at each complex place $w$ it is $x\mapsto\|x\|^{\mathrm{mult}(w)\,uC_w}(x/\|x\|)^{kC_w}$ (the predicate `IsArchCompAt`).
--
--   The character $\omega$ on $(\mathbb A_{\mathbb Q})^\times$ is subject to `hω`, a conjunction of three clauses: $\omega$ is an admissible twist; at every prime $p$ of $\mathcal O_{\mathbb Q}$ which is not a bad place for $(K,\mu)$ — bad meaning ramified in $K$ or carrying a prime of $K$ above it at which $\mu$ is ramified — $\omega$ is unramified and its Euler coefficient $\omega(\varpi_p)$ equals `inducedE3 ℚ (inducedCoeff K μ) p`, the negative of the degree-$3$ coefficient of the induced Euler polynomial formed from the unramified coefficients of $\mu$; and, for every choice of archimedean parameter families for $\mu$ as above, the archimedean component of $\omega$ at each real place $v$ of $\mathbb Q$ has exponent $\sum_{w\ \mathrm{real}}uR_w+\sum_{w\ \mathrm{complex}}2\,uC_w$ and sign exponent $\sum_{w\ \mathrm{real}}(aR_w).\mathrm{val}+\sum_{w\ \mathrm{complex}}(kC_w+1)$ (finite sums over the infinite places).
--
--   Archimedean frame. $E\colon(\mathbb A_{\mathbb Q,\infty})^\times\to(\mathbb A_{\mathbb Q})^\times$ is a splitting of the infinite part: by `hE`, the infinite component of $E(u)$ is $u$ and its finite component is $1$. A rational number $a$ is fixed with $a\neq0$ and $a=-1$; $a_{\inf}$ is an infinite idele unit whose underlying element is the image of $a$; $\psi_\infty$ is the additive character $x\mapsto\psi_{\mathrm{arch}}(a\,x)$ obtained from the standard archimedean character. Measures: $\nu_{\mathrm{add}}$ on $\mathbb A_{\mathbb Q,\infty}$ is $|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the mixed-space ring equivalence, and $\nu_{\mathrm{mul}}$ is a Haar measure on $(\mathbb A_{\mathbb Q,\infty})^\times$; the relevant Borel structures are fixed.
--
--   The $GL_2(\mathbb R)$ Whittaker profile. $P$ is a real archimedean parameter, i.e. either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb C$, $a_i\in\mathbb Z/2$, or $\mathrm{discrete}(u,k)$ with $k\ge1$; `_hP₁` requires $|\Re(u_1-u_2)|<1$ in the principal case. Data $kw$ (weights), $Wr$ (torus profiles on $\mathbb R$) and $WA$ (functions on $GL_2(\mathbb R)$), all indexed by a parity $par\in\mathbb Z/2$, satisfy: `hkw1`, in the principal case $kw(par,w)=[a_1+par]+[a_2+par]$, where $[\,\cdot\,]=\mathrm{signShift}$ is $0$ on $0$ and $1$ otherwise; `hkw2`, in the discrete case $P=\mathrm{discrete}(u_0,n)$ one has $kw(par,w)=n+1$; `hWr1`, in the principal case with equal signs $a_1=a_2$ and $par=a_1$, $Wr(par,w,-t)=(-1)^{a_1.\mathrm{val}}Wr(par,w,t)$; `hWr2`, in the discrete case $Wr(par,w,t)=0$ for $t<0$; `hWr3`, in the principal case with $a_1=a_2$ and $par=a_1+1$, the Mellin transform of $t\mapsto(Wr(par,w,t)+(-1)^{a_1.\mathrm{val}}Wr(par,w,-t))/t$ converges in a right half-plane and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}(0,a_1)$; `hWr4`, for every $par$ and every $b$ with $b=par$ or $b=par+P.\mathrm{centralSign}$, the same Mellin transform with $(-1)^{b.\mathrm{val}}$ converges in a right half-plane and equals the archimedean factor of $P.\mathrm{twist}(0,b)$. (In the branch fixed below $P$ is of discrete type, so the principal-case clauses `_hP₁`, `hkw1`, `hWr1`, `hWr3` carry no content.) The function $WA(par)$ satisfies: `hWAN`, $WA(par)(n(x)h)=e^{-2\pi i a x}WA(par)(h)$ for the unipotent $n(x)$; `hWAZ`, $WA(par)(z\cdot h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}WA(par)(h)$ for scalar $z\in\mathbb R^\times$; `hWAK`, $WA(par)(h\kappa)=\mathrm{archWeightChar}_{\mathbb R}(kw(par,\mathrm{default}))(\kappa)\,WA(par)(h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt`, $WA(par)(\mathrm{diagOne}\,t)=Wr(par,\mathrm{default},t)$ for $t\in\mathbb R^\times$, where $\mathrm{default}$ is the unique (real) infinite place of $\mathbb Q$; and `hWAc`, continuity of each $WA(par)$. Finally $w_{0R}\in GL_2(\mathbb R)$ has matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   The Levi sheet. $w_0$ is a real infinite place of $K$. The second real archimedean parameter $P_2$ is constrained by `hP₂` to one of two shapes: either $K$ has exactly three infinite places $w_0,w_1,w_2$, all real and pairwise distinct, and $P_2=\mathrm{principal}(uR_{w_1},aR_{w_1},uR_{w_2},aR_{w_2})$; or $K$ has exactly the two infinite places $w_0$ and a complex place $w_C$, and then either $kC_{w_C}\neq0$ and $P_2=\mathrm{discrete}(uC_{w_C},|kC_{w_C}|)$, or $kC_{w_C}=0$ and $P_2=\mathrm{principal}(uC_{w_C},0,uC_{w_C},1)$. $D$ is an `ArchDatumR P₂`: a function $D.W$ on $2\times2$ real matrices, smooth on the invertible locus, transforming by $\psi$ under the unipotent and by the central character of $P_2$ times $|z|$ under scalars, equipped with entire completed zeta functions having the prescribed Mellin integral representations, functional equation with epsilon factor $(P_2.\mathrm{twist}(u,a)).\mathrm{epsilonFactor}$, finite order in vertical strips, and the stated decay at large and small torus parameter. With $k_0\in\mathbb Z$: `hDW` gives right equivariance $D.W(x\kappa)=\mathrm{archWeightChar}_{\mathbb R}(k_0)(\kappa)\,D.W(x)$ for $\kappa\in$ `rowIsometrySubgroup₀ ℝ`; `hDE` says $D$ is a Casimir eigenfunction with eigenvalue $P_2.\mathrm{laplaceEigenvalue}$; `hDnz` says $D.W$ is not identically zero on $GL_2(\mathbb R)$; `hk₀min` says that in the principal case $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, and in the discrete case $k_0=m+1$ for the discrete index $m$.
--
--   The branch. $P=\mathrm{discrete}(u_P,n_P)$ with $n_P\ge1$ (`hPdisc`), and $m=n_P+1$. A natural number $n$ and a sign $\varepsilon'$ satisfy `hcol`: either $\varepsilon'=-1$ and $n=k_0-m$, or $\varepsilon'=1$ and $n=m-k_0$. A parity $par_0$ is fixed. The section $S$ on $2\times3$ real matrices is given by `hS`:
--   $$S(M)=\big((M_{00}-iM_{10})-i(M_{01}-iM_{11})\big)^m\,\big(M_{02}+\varepsilon' i M_{12}\big)^n\,e^{-\pi\sum_{i,b}M_{ib}^2}.$$
--   The profile at $par_0$ is explicit: $Wr(par_0,\mathrm{default},t)=2\,t^{\,u_P+n_P/2+1}e^{-2\pi t}$ for $t>0$ (`hWpos`) and $0$ for $t<0$ (`hWneg`). Moreover $k_0=1$ (`hk₀`), and $P_2=\mathrm{principal}(\mu_1,c_1,\mu_2,c_2)$ (`hP₂eq`) with $c_1\neq c_2$ (`hc`). A scalar $\rho\in\mathbb C$ is such that (`hD`) for all $b\in\mathbb Z/2$ and $\tau>0$,
--   $$D.W(\mathrm{diagOne}\,\tau)+(-1)^{b.\mathrm{val}}D.W(\mathrm{diagOne}(-\tau))=\rho\,\tau\cdot 4\int_0^\infty r^{\mu_1+[c_1+b]}e^{-\pi r^2}\,(\tau/r)^{\mu_2+[c_2+b]}e^{-\pi(\tau/r)^2}\,\frac{dr}{r},$$
--   a multiplicative convolution of two Gaussians.
--
--   Conclusion. There exists $\sigma_a\in\mathbb R$ such that for every $s\in\mathbb C$ with $\Re s>\sigma_a$ the following identity holds. On the left stands the iterated integral over $a_2\in(0,\infty)$ and $a_1\in\mathbb R$ whose integrand vanishes unless $a_1\neq0$ and $a_2>0$, and in that case, with $q=\mathrm{upperUnit}(a_1,0,a_2)=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}\in GL_2(\mathbb R)$, equals
--   $$\Big(|\det q|\;WA(par_0)\big(w_{0R}\cdot{}^t q^{-1}\big)\Big)\cdot \mathrm{dualWhittakerFn3}\big(\mathrm{jacquetVector3}\,D\,uR_{w_0}\,aR_{w_0}\,a\,\psi_\infty\,S\big)\big(\iota(q)_\infty\big)\cdot|\det q|^{\,s-1/2}\cdot a_1^{-2},$$
--   where $\iota(q)_\infty$ denotes the image of $q$ in $GL_3(\mathbb A_{\mathbb Q,\infty})$ obtained by embedding $q$ at the real place $\mathrm{default}$ of $\mathbb Q$ into adelic $GL_2$, then by the block embedding $\iota$ into adelic $GL_3$, then by taking the archimedean component, and where $\mathrm{dualWhittakerFn3}(W)(g)=W(\mathrm{longWeyl3}\cdot{}^tg^{-1})$. The right-hand side is
--   $$\pi\,i^{m}(-1)^{m+n+(aR_{w_0}).\mathrm{val}}\,2^{m}\;\Gamma_{\mathbb R}\big(2s-P.\mathrm{centralExponent}-P_2.\mathrm{centralExponent}+n+1\big)\;(2\pi)^{-A}\,\Gamma(A)\;\cdot\;\rho\,\Gamma_{\mathbb R}\big(2Z'+\mu_1+\mu_2+1\big)\Big[B\big(Z'+\mu_1+[c_1],\,Z'+\mu_2+[c_2]\big)+B\big(Z'+\mu_1+[c_1+1],\,Z'+\mu_2+[c_2+1]\big)\Big],$$
--   where $A=s-uR_{w_0}-u_P+m/2$, $Z'=s-u_P-P_2.\mathrm{centralExponent}+m/2$, $B$ is the Beta integral, and $P.\mathrm{centralExponent}=2u_P$, $P_2.\mathrm{centralExponent}=\mu_1+\mu_2$.
--
--   This is the dual (reflected) torus-integral computation in the Rankin–Selberg analysis of the cubic induction of a Hecke character $\mu$ of a cubic field, in the branch where the $GL_2(\mathbb R)$ profile is of discrete-series type, the Levi parameter $P_2$ is principal with distinct signs, and the Levi weight is $k_0=1$: the unfolded integral of $WA(par_0)$ against the dual Whittaker function of the Jacquet vector of the degree-$(m,n)$ Gaussian section is evaluated in raw closed form as a product of $\Gamma_{\mathbb R}$ and $\Gamma$ factors with a sum of two Beta integrals at the dual argument, no root-number extraction being performed. It feeds the two assembly statements `exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_oneComplex_weightOneLevi` and `…_of_threeReal_oppSign`, where the primal and dual pairs are compared to produce the archimedean functional equation required by the converse theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_dualTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_weightOneLevi.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_weightOneLevi
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
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = (Real.pi : ℂ) * Complex.I ^ m * (-1 : ℂ) ^ (m + n + (aR w₀ h₀).val) * (2 : ℂ) ^ m *
              Complex.Gammaℝ (2 * s - P.centralExponent - P₂.centralExponent + (n : ℂ) + 1) *
              (2 * (Real.pi : ℂ)) ^ (-(s - uR w₀ h₀ - uP + (m : ℂ) / 2)) * Complex.Gamma (s - uR w₀ h₀ - uP + (m : ℂ) / 2) *
              (ρ * Complex.Gammaℝ (2 * (s - uP - P₂.centralExponent + (m : ℂ) / 2) + μ₁ + μ₂ + 1) *
                (Complex.betaIntegral ((s - uP - P₂.centralExponent + (m : ℂ) / 2) + μ₁ + signShift c₁) ((s - uP - P₂.centralExponent + (m : ℂ) / 2) + μ₂ + signShift c₂) +
                 Complex.betaIntegral ((s - uP - P₂.centralExponent + (m : ℂ) / 2) + μ₁ + signShift (c₁ + 1)) ((s - uP - P₂.centralExponent + (m : ℂ) / 2) + μ₂ + signShift (c₂ + 1)))) := by sorry
