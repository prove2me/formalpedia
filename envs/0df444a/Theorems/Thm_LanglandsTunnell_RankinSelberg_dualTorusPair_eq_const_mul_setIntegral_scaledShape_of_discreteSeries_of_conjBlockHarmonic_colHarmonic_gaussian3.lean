-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/e3d5537d-3575-51ac-8b13-f61816136041
-- title:
--   Unfolded dual torus pair as 4π i^m times scaled-shape integral
-- statement:
--   Throughout, $K$ is a number field equipped with an algebra structure of $\mathcal O_{\mathbb Q}$ on $\mathcal O_K$ which is integral, and $\mathrm{finrank}_{\mathbb Q}K = 3$ (hypothesis `_hdeg`).
--
--   **The character of $K$ and its archimedean exponents.** A continuous homomorphism $\mu\colon (\mathbb A_K)^\times \to \mathbb C^\times$ is assumed to be an admissible twist, i.e. trivial on the principal ideles $K^\times$, continuous, and of absolute value $1$ everywhere (`_hμ`). The hypothesis `_hns` asserts that no admissible twist $\eta$ of $\mathbb Q$ exists with the property that for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and whose trace $p=\mathfrak P\cap\mathcal O_{\mathbb Q}$ carries $\eta$ unramified, the value $\mu$ of a uniformiser idele at $\mathfrak P$ equals the corresponding value of $\eta$ at $p$ raised to the inertia degree $f(\mathfrak P/p)$; here "unramified at $v$" means that the local character is trivial on the units of the valuation ring. Families $u_R(w)$, $a_R(w)\in\mathbb Z/2$ (for the real places $w$ of $K$) and $u_C(w)$, $k_C(w)\in\mathbb Z$ (for the complex ones) are given, and `huR`, `huC` require that for each archimedean place the local component of $\mu$ on $(K_w)^\times$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,u}\,(x/\|x\|)^{a}$ with $u=u_R(w)$, $a=(a_R(w)).\mathrm{val}$ in the real case and $u=u_C(w)$, $a=k_C(w)$ in the complex case.
--
--   **The comparison character on $\mathbb Q$.** A homomorphism $\omega\colon(\mathbb A_{\mathbb Q})^\times\to\mathbb C^\times$ is given together with the threefold hypothesis `hω`: $\omega$ is an admissible twist of $\mathbb Q$; at every prime $p$ of $\mathcal O_{\mathbb Q}$ which is not a bad place for $(K,\mu)$ — bad meaning that $p$ is ramified in $K$, or that $\mu$ is ramified at some prime of $K$ above $p$ — the character $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\text{uniformiser idele at }p)$ equals $-$(the degree-$3$ coefficient of the induced Euler polynomial formed from the coefficients $\mathfrak P\mapsto \mu(\text{uniformiser at }\mathfrak P)$, extended by $0$ at ramified $\mathfrak P$); and, for any data $u_R,a_R,u_C,k_C$ satisfying the same archimedean conditions as above, at each real place $v$ of $\mathbb Q$ the archimedean component of $\omega$ has exponent $\sum_{w\ \mathrm{real}}u_R(w)+\sum_{w\ \mathrm{complex}}2u_C(w)$ and integer parameter $\sum_{w\ \mathrm{real}}(a_R(w)).\mathrm{val}+\sum_{w\ \mathrm{complex}}(k_C(w)+1)$ (finite sums over places).
--
--   **Adelic and measure-theoretic frame.** A monoid homomorphism $E\colon(\mathbb A_{\mathbb Q,\infty})^\times\to(\mathbb A_{\mathbb Q})^\times$ is given with `hE`: the infinite part of $E(u)$ is $u$ and its finite part is $1$. A rational number $a\neq 0$ with $a=-1$ is fixed, together with an infinite idele $a_\infty$ whose underlying element is the image of $a$, and an additive character $\psi_\infty$ of $\mathbb A_{\mathbb Q,\infty}$ with $\psi_\infty(x)=\psi_{\mathrm{arch}}(a x)$ for the standard archimedean character (`hpsiInf`). Measurable and Borel structures on $\mathbb A_{\mathbb Q,\infty}$ and on its unit group are assumed; $\nu_{\mathrm{add}}$ is the measure $|a|^{1/2}$ times the transport of Lebesgue measure along the inverse of the ring equivalence with the mixed space (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on $(\mathbb A_{\mathbb Q,\infty})^\times$.
--
--   **The $\mathrm{GL}_2(\mathbb R)$ Whittaker data at the real place of $\mathbb Q$.** A real archimedean parameter $P$ is given, with `_hP₁` requiring $|\mathrm{Re}(u_1-u_2)|<1$ whenever $P$ is principal with data $(u_1,a_1,u_2,a_2)$. Data $k_w\colon\mathbb Z/2\times\{\text{places}\}\to\mathbb Z$, $W_r\colon\mathbb Z/2\times\{\text{places}\}\to(\mathbb R\to\mathbb C)$ and $W_A\colon\mathbb Z/2\to(\mathrm{GL}_2(\mathbb R)\to\mathbb C)$ are subject to: `hkw1`, `hkw2` pinning the weight, namely $k_w(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ in the principal case (where $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$) and $k_w(\mathrm{par},w)=n+1$ in the discrete case of weight $n$; `hWr1` (symmetry $W_r(-t)=(-1)^{a_1}W_r(t)$ in the principal case with equal signs and matching parity), `hWr2` (vanishing on $t<0$ in the discrete case), and `hWr3`, `hWr4`, which assert Mellin convergence in a right half-plane of $t\mapsto (W_r(t)+(-1)^{b}W_r(-t))/t$ together with the values $\frac{2s+u_1+u_2-1}{4\pi}\,\Gamma$-factor of the twist $(P,0,a_1)$ in the case $\mathrm{par}=a_1+1$ of a principal $P$ with equal signs, respectively the $\Gamma$-factor of the twist $(P,0,b)$ for $b=\mathrm{par}$ or $b=\mathrm{par}+\mathrm{centralSign}(P)$; and the Whittaker transformation laws `hWAN` (left translation by the upper unipotent $x$ multiplies $W_A$ by $e^{-2\pi i a x}$), `hWAZ` (left translation by the scalar $z$ multiplies it by $|z|^{\,\mathrm{centralExponent}(P)+1}(z/|z|)^{\mathrm{centralSign}(P)}$), `hWAK` (right translation by $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ` multiplies it by $\mathrm{archWeightChar}_{\mathbb R}(k_w(\mathrm{par},\ast))(\kappa)$), `hWAt` ($W_A(\mathrm{par})$ restricted to $\mathrm{diag}(t,1)$ is $W_r(\mathrm{par},\ast)(t)$) and `hWAc` (continuity). The element $w_{0,\mathbb R}\in\mathrm{GL}_2(\mathbb R)$ has matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   **The complementary archimedean datum.** A real place $w_0$ of $K$ is fixed, and a second real archimedean parameter $P_2$ subject to `hP₂`: either $K$ has exactly three real places $w_0,w_1,w_2$ (pairwise distinct and exhausting all places) and $P_2$ is principal with data $(u_R(w_1),a_R(w_1),u_R(w_2),a_R(w_2))$, or $K$ has one complex place $w_C$ besides $w_0$ which together exhaust all places, and then $P_2$ is the discrete parameter with exponent $u_C(w_C)$ and weight $|k_C(w_C)|$ when $k_C(w_C)\neq 0$, and the principal parameter $(u_C(w_C),0,u_C(w_C),1)$ when $k_C(w_C)=0$. An archimedean datum $D$ for $P_2$ is given — a function $D.W$ on $2\times2$ real matrices, smooth on the invertible locus, with $D.W(n(x)g)=\psi(x)D.W(g)$, central law $D.W(zg)=\mathrm{centralChar}(P_2)(z)\,|z|\,D.W(g)$ for $z\neq0$, and entire zeta-integral data realising the $\Gamma$-factors of the twists of $P_2$, satisfying the functional equation with the $\varepsilon$-factor of $P_2$, of finite order in vertical strips, with the prescribed decay at large and small $y$ — together with an integer $k_0$ and: `hDW`, that right translation by $r\in$ `rowIsometrySubgroup₀ ℝ` multiplies $D.W$ by $\mathrm{archWeightChar}_{\mathbb R}(k_0)(r)$; `hDE`, that $D$ is a Casimir eigenfunction, i.e. $\mathrm{matrixCasimir}(D.W)(x)=\mathrm{laplaceEigenvalue}(P_2)\,D.W(x)$ for all $x$ with $\det x\neq0$; `hDnz`, that $D.W$ does not vanish identically on $\mathrm{GL}_2(\mathbb R)$; and `hk₀min`, that $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2 \pmod 2$ when $P_2$ is principal with signs $a_1,a_2$, and $k_0=m'+1$ when $P_2$ is discrete of weight $m'$.
--
--   **Discrete-series specialisation and the flat section.** It is assumed that $P$ is the discrete parameter with exponent $u_P$ and weight $n_P\ge1$ (`hPdisc`), that $m=n_P+1$, and that a natural number $n$ and a sign $\varepsilon'$ satisfy `hcol`: either $\varepsilon'=-1$ and $n=k_0-m$, or $\varepsilon'=1$ and $n=m-k_0$. A parity $\mathrm{par}_0\in\mathbb Z/2$ is fixed. The Schwartz datum $S$ on $2\times3$ real matrices is
--   $$S(M)=\bigl((M_{00}-iM_{10})-i(M_{01}-iM_{11})\bigr)^m\,\bigl(M_{02}+\varepsilon' i M_{12}\bigr)^n\,e^{-\pi\sum_{i,b}M_{ib}^2}.$$
--   Finally `hWpos` and `hWneg` give the explicit discrete-series profile: $W_r(\mathrm{par}_0,\ast)(t)=2\,t^{\,u_P+n_P/2+1}e^{-2\pi t}$ for $t>0$, and $W_r(\mathrm{par}_0,\ast)(t)=0$ for $t<0$.
--
--   **Conclusion.** Write $u_{w_0}=u_R(w_0)$, $Q=u_P+\tfrac{n_P}{2}+1$, and let $c(P)$, $c(P_2)$ denote the central exponents of $P$ and $P_2$ (so $c(P)=2u_P$ by `hPdisc`). Then for *every* $s\in\mathbb C$ — no half-plane condition is imposed — the following identity of integrals holds. On the left, for $a_2\in(0,\infty)$ and $a_1\in\mathbb R$ the integrand is $0$ unless $a_1\neq0$ and $a_2>0$, in which case, with $q=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$ viewed in $\mathrm{GL}_2(\mathbb R)$, it equals
--   $$|\det q|\cdot W_A(\mathrm{par}_0)\bigl(w_{0,\mathbb R}\cdot{}^{t}q^{-1}\bigr)\cdot \Lambda\bigl(\iota(q)\bigr)\cdot|\det q|^{\,s-1/2}\cdot a_1^{-2},$$
--   where $\iota(q)$ is $q$ placed at the real place of $\mathbb Q$ inside the adelic $\mathrm{GL}_2$, pushed into $\mathrm{GL}_3$ by the block embedding and projected to its infinite-adelic component, and $\Lambda$ is the dual Whittaker function attached to the Jacquet vector $\mathrm{jacquetVector3}\,D\,u_{w_0}\,a_R(w_0)\,a\,\psi_\infty\,S$, namely $g\mapsto \mathrm{jacquetVector3}(\dots)(w_3\cdot {}^{t}g^{-1})$ with $w_3$ the long Weyl element of $\mathrm{GL}_3$; recall that $\mathrm{jacquetVector3}$ is the quasicharacter $\mathrm{quasiChar}(u_{w_0}+1,a_R(w_0))$ of the determinant of the real matrix of $g$ times the integral over $e\in M_2(\mathbb R)$ of the Jacquet integrand. The assertion is that this iterated integral, $\int_{a_2\in(0,\infty)}\int_{a_1\in\mathbb R}$, equals
--   $$4\pi\, i^{\,m}\int_{0}^{\infty}\!\!\int_{-\infty}^{0}|a_1|^{\,s+Q-c(P)-u_{w_0}-\frac32}\;a_2^{\,s-Q-u_{w_0}+\frac12}\;e^{-2\pi|a_1|/a_2}\;I(a_1,a_2)\;da_1\,da_2,$$
--   where the inner factor is the iterated integral over $y_1\in\mathbb R$ and then $y_2\in(0,\infty)$
--   $$I(a_1,a_2)=\int_{\mathbb R}\!\int_{0}^{\infty}(y_1^{-1})^{n}\,\sigma(y_1)\,|y_1|^{-(u_{w_0}+2)}\,y_2^{\,c(P_2)-u_{w_0}}\,e^{-\pi\left((a_2y_2)^{-2}+y_1^{-2}+a_1^2y_2^2+a_2^2y_1^2\right)}\,D.W\!\left(\mathrm{diag}\!\left(a\,\tfrac{y_1}{y_2},1\right)\right)\,J(a_1,a_2,y_1,y_2)\,dy_2\,dy_1,$$
--   with $\sigma(y_1)=1$ if $a_R(w_0)=0$ and $\sigma(y_1)=\mathrm{sign}(y_1)$ otherwise, and with the Gaussian moment
--   $$J(a_1,a_2,y_1,y_2)=\int_{\mathbb R}\bigl(a_1y_2-(a_2y_2)^{-1}+a_2y_1+iz\bigr)^{m}e^{-\pi z^{2}}\,dz.$$
--   The outer variable on the right runs over $a_2\in(0,\infty)$ and the next over $a_1\in(-\infty,0)$ only; the right-hand side involves only the archimedean objects $D$, $P$, $P_2$, $u_{w_0}$, $a_R(w_0)$, $m$, $n$ and $a$.
--
--   This is the unfolding step on the dual side of the Rankin–Selberg computation for the cubic induced representation, rewriting the $\mathrm{GL}_2\times\mathrm{GL}_3$ dual torus pair attached to a discrete-series archimedean profile and the degree-$m$ conjugate-harmonic flat section as an explicit four-fold integral of scaled shape, valid for all $s$. It is used by the corresponding existence statement [`LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3), which feeds the archimedean comparison in the converse-theorem argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3.lean

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

theorem LanglandsTunnell.RankinSelberg.dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
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
    ∀ s : ℂ,
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = 4 * (Real.pi : ℂ) * Complex.I ^ m *
              ∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ in Set.Iio (0 : ℝ),
                ((|a₁| : ℝ) : ℂ) ^ (s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) *
                  ((a₂ : ℝ) : ℂ) ^ (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) *
                  (Real.exp (-(2 * Real.pi * (|a₁| / a₂))) : ℂ) *
                ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ),
                  ((y₁⁻¹ : ℝ) : ℂ) ^ n * (if aR w₀ h₀ = 0 then (1 : ℂ) else ((SignType.sign y₁ : ℝ) : ℂ)) *
                    ((|y₁| : ℝ) : ℂ) ^ (-(uR w₀ h₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ (P₂.centralExponent - uR w₀ h₀) *
                    (Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2 + a₂ ^ 2 * y₁ ^ 2))) : ℂ) *
                    (fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v))) (y₁ / y₂) *
                    (∫ z : ℝ, (((a₁ * y₂ - (a₂ * y₂)⁻¹ + a₂ * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
                      (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) := by sorry
