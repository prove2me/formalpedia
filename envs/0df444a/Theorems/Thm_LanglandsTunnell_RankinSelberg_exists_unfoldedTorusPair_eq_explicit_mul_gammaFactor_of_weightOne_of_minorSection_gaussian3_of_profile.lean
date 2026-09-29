-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_minorSection_gaussian3_of_profile
-- name    : LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_minorSection_gaussian3_of_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/22f68f1e-8a8f-5505-a35d-72155938e076
-- title:
--   Explicit primal torus pair for the minor-section Jacquet vector
-- statement:
--   The setting is a number field $K$ carrying an $\mathcal O_{\mathbb Q}$-algebra structure on $\mathcal O_K$ which is integral, together with the hypothesis `_hdeg` that $[K:\mathbb Q]=3$, and a homomorphism $\mu$ from the idele units of $K$ to $\mathbb C^\times$ which is an admissible twist, i.e. trivial on the principal ideles coming from $K^\times$, continuous, and of absolute value $1$ everywhere. The hypothesis `_hns` excludes base change: there is no admissible twist $\eta$ of $\mathbb Q$ such that for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and whose prime $p=\mathfrak P\cap\mathcal O_{\mathbb Q}$ carries an unramified $\eta$, the value of $\mu$ on the uniformiser idele at $\mathfrak P$ equals the value of $\eta$ on the uniformiser idele at $p$ raised to the inertia degree of $\mathfrak P$ over $p$.
--
--   The archimedean components of $\mu$ are recorded by families $uR,aR$ indexed by the real places and $uC,kC$ indexed by the complex places: `huR` says that at each real place $w$ the local component of $\mu$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,uR(w)}\,(x/\|x\|)^{(aR(w))^{\mathrm{val}}}$, and `huC` says the same at each complex place with exponent $uC(w)$ and integer $kC(w)$.
--
--   A homomorphism $\omega$ on the idele units of $\mathbb Q$ is given, and `hω` has three conjuncts: $\omega$ is an admissible twist of $\mathbb Q$; at every prime $p$ of $\mathcal O_{\mathbb Q}$ which is not a bad place for $(K,\mu)$ — that is, $p$ is unramified in $K$ and $\mu$ is unramified at every prime of the fibre over $p$ — the character $\omega$ is unramified at $p$ and its Euler coefficient (the value of $\omega$ on the uniformiser idele at $p$) equals `inducedE3 ℚ (inducedCoeff K μ) p`, the negative of the coefficient of $X^3$ in the induced Euler polynomial formed from the unramified values of $\mu$; and, for every choice of archimedean data $uR,aR,uC,kC$ satisfying the two conditions above, at every real place $v$ of $\mathbb Q$ the local component of $\omega$ has exponent $\sum_w uR(w)+\sum_w 2\,uC(w)$ and integer parameter $\sum_w (aR(w))^{\mathrm{val}}+\sum_w (kC(w)+1)$, the sums being finite sums over the real, respectively complex, places of $K$.
--
--   The archimedean frame consists of: a homomorphism $E$ from the units of the infinite adele ring of $\mathbb Q$ to the idele units, with `hE` asserting that $E(u)$ has infinite part $u$ and trivial finite part; a nonzero rational $a$ with `ha1` fixing $a=-1$; an infinite idele unit $a_{\infty}$ whose underlying element is the image of $a$; an additive character $\psi_{\infty}$ of the infinite adele ring with $\psi_\infty(x)=\psi_{\mathrm{arch}}(a x)$ for the standard archimedean character; measurable and Borel structures on the infinite adele ring and on its unit group; a measure $\nu_{\mathrm{add}}$ equal to $|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the ring equivalence of the infinite adele ring with the mixed space; and a Haar measure $\nu_{\mathrm{mul}}$ on the unit group.
--
--   The archimedean parameter of the twisted representation is a `RealArchParam` $P$, subject to `_hP₁`: whenever $P=\mathrm{principal}\,u_1\,a_1\,u_2\,a_2$ one has $|\mathrm{Re}(u_1-u_2)|<1$. Attached to $P$ are a weight function $kw$, a family of functions $Wr$ on $\mathbb R$ and a family $WA$ on $GL_2(\mathbb R)$, all indexed by a parity in $\mathbb Z/2$ (and by a place of $\mathbb Q$ for $kw$ and $Wr$), with the following hypotheses. The weight clauses: `hkw1`, in the principal case, $kw(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$; `hkw2`, in the discrete case with parameter $n\ge 1$, $kw(\mathrm{par},w)=n+1$. The radial clauses: `hWr1`, if $P=\mathrm{principal}\,u_1\,a_1\,u_2\,a_1$ and $\mathrm{par}=a_1$, then $Wr(\mathrm{par},w,-t)=(-1)^{a_1^{\mathrm{val}}}Wr(\mathrm{par},w,t)$ for all real $t$; `hWr2`, in the discrete case $Wr(\mathrm{par},w,t)=0$ for $t<0$; `hWr3`, if $P=\mathrm{principal}\,u_1\,a_1\,u_2\,a_1$ and $\mathrm{par}=a_1+1$, then there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (Wr(\mathrm{par},w,t)+(-1)^{a_1^{\mathrm{val}}}Wr(\mathrm{par},w,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P$ twisted by $(0,a_1)$ at $s$; `hWr4`, for every $b$ equal to $\mathrm{par}$ or to $\mathrm{par}+P.\mathrm{centralSign}$, there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (Wr(\mathrm{par},w,t)+(-1)^{b^{\mathrm{val}}}Wr(\mathrm{par},w,-t))/t$ converges and equals the archimedean factor of $P$ twisted by $(0,b)$ at $s$. The Whittaker clauses for $WA$: `hWAN`, $WA(\mathrm{par},n(x)h)=\exp(-2\pi i a x)\,WA(\mathrm{par},h)$ for the unipotent $n(x)$; `hWAZ`, for a scalar matrix with entry $z$, $WA(\mathrm{par},z\,h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}^{\mathrm{val}}}WA(\mathrm{par},h)$; `hWAK`, right equivariance $WA(\mathrm{par},h\kappa)=\mathrm{archWeightChar}_{\mathbb R}(kw(\mathrm{par},\mathrm{default}))(\kappa)\,WA(\mathrm{par},h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt`, restriction to the torus, $WA(\mathrm{par},\mathrm{diag}(t,1))=Wr(\mathrm{par},\mathrm{default},t)$; and `hWAc`, continuity of each $WA(\mathrm{par},\cdot)$. An element $w_{0}^{\mathbb R}$ of $GL_2(\mathbb R)$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ is also fixed.
--
--   On the side of the cubic datum: a real place $w_0$ of $K$, a second parameter $P_2$, and `hP₂` giving the two possible archimedean profiles of $K$ apart from $w_0$ — either $K$ has exactly three distinct real places $w_0,w_1,w_2$ and $P_2=\mathrm{principal}\,(uR\,w_1)\,(aR\,w_1)\,(uR\,w_2)\,(aR\,w_2)$, or $K$ has a complex place $w_C$ and the only places are $w_C$ and $w_0$, with $P_2=\mathrm{discrete}\,(uC\,w_C)\,|kC\,w_C|$ when $kC\,w_C\neq 0$ and $P_2=\mathrm{principal}\,(uC\,w_C)\,0\,(uC\,w_C)\,1$ when $kC\,w_C=0$. Further, $D$ is an archimedean datum `ArchDatumR P₂` (a function $D.W$ on real $2\times2$ matrices, smooth on the invertible locus, with the unipotent and central transformation laws for $P_2$, entire zeta functions satisfying the functional equation, finite order and the prescribed decay), $k_0$ is an integer, and: `hDW`, $D.W$ is right equivariant under `rowIsometrySubgroup₀ ℝ` by $\mathrm{archWeightChar}_{\mathbb R}(k_0)$; `hDE`, $D$ satisfies the Casimir eigenvalue equation with eigenvalue $P_2.\mathrm{laplaceEigenvalue}$ at every matrix of nonzero determinant; `hDnz`, $D.W$ does not vanish identically; `hk₀min`, in the principal case $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2 \pmod 2$, and in the discrete case with parameter $m$ one has $k_0=m+1$. Three further constraints pin down the configuration: `hPw1`, $P$ is principal with unequal parities $a_1\neq a_2$ (weight one); `hk₀`, $k_0=0$ (weight zero); `hodd`, whenever $P_2=\mathrm{principal}\,u_1\,a_1\,u_2\,a_2$ one has $aR(w_0)\neq a_1$.
--
--   Finally a parity $par_0$ is fixed, and the minor section $S$ on $2\times 3$ real matrices is given by `hS`:
--   $$S(M)=\bigl((M_{00}-iM_{01})M_{12}-(M_{10}-iM_{11})M_{02}\bigr)\exp\Bigl(-\pi\sum_{i<2}\sum_{b<3}M_{ib}^{2}\Bigr).$$
--   The last group of data specialises $P_2$ and the torus profile of $D$: complex numbers $u_1,u_2$ and a parity $c$ with `hP₂eq` $P_2=\mathrm{principal}\,u_1\,c\,u_2\,c$, and a complex number $\rho$ with `hρ`: for every $\tau>0$,
--   $$D.W(\mathrm{diag}(\tau,1))=\rho\,\tau\cdot 4\int_{0}^{\infty} r^{u_1}e^{-\pi r^{2}}\,(\tau/r)^{u_2}e^{-\pi(\tau/r)^{2}}\,\frac{dr}{r}.$$
--
--   Under these hypotheses the assertion is: there exists $\sigma_a\in\mathbb R$ such that for every $s\in\mathbb C$ with $\mathrm{Re}\,s>\sigma_a$, the integral over all $2\times2$ real matrices $e$ (Lebesgue measure) of
--   $$\mathrm{quasiChar}\bigl(uR(w_0)+2,\ aR(w_0)\bigr)(\det e)\cdot |\det e|^{-2}\cdot I_1(e,s)\cdot I_2(e,s),$$
--   where $\mathrm{quasiChar}(u,a)(y)=|y|^{u}$ times $1$ if $a=0$ and times $\mathrm{sign}(y)$ otherwise,
--   $$I_1(e,s)=\int_{\mathbb R} Wr(par_0,\mathrm{default},t)\; D.W\bigl(\mathrm{diag}(at,1)\,e^{-1}\bigr)\;|t|^{\,s-1/2}\,t^{-2}\,dt,$$
--   $$I_2(e,s)=\int_{0}^{\infty} y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\;\mathrm{godementInner3}\bigl(\psi_{\infty}\cdot_{\mathrm{shift}}\iota(y)\bigr)\,S\,(e)\,1\;dy,$$
--   with $\iota(y)$ the infinite adele all of whose components are the real number $y$ and $\mathrm{godementInner3}(\psi,S,h,m)=\int_{\mathbb R^{2}}S\bigl(h\cdot(m_{0\bullet}+v_0m_{2\bullet},\,m_{1\bullet}+v_1m_{2\bullet})\bigr)\,\psi(\iota(-v_1))\,dv$ evaluated at $m$ the identity $3\times3$ matrix, equals
--   $$\bigl(\pi\, i\,(-1)^{c^{\mathrm{val}}}\rho\bigr)\cdot\prod_{x}\Gamma_{\mathbb R}\bigl(s+\tfrac12+x\bigr)\cdot\prod_{x}\Gamma_{\mathbb C}\bigl(s+\tfrac12+x\bigr),$$
--   the first product being over the multiset `twistedGammaR K (archOfParamR K P) uR aR`, that is the sum over the real places $w$ of $K$ of the real gamma shifts of $P$ twisted by $(uR(w),aR(w))$, and the second over the multiset `twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC`, that is the sum of the complex gamma shifts of those same twists at the real places together with the complex gamma shifts of the base change of $P$ twisted by $(uC(w),kC(w))$ at the complex places.
--
--   This is the primal half of the archimedean Rankin–Selberg computation for the cubic induced representation attached to $(K,\mu)$, in the configuration where the twisted parameter $P$ has weight one, the Levi datum $D$ has weight zero and odd relative parity, and the Jacquet vector is built from the minor section $S$ of the Gaussian on $2\times3$ matrices; the constant is made explicit as $\pi i(-1)^{c}\rho$ in terms of the torus profile of $D$. It feeds the combined primal-and-dual torus-pair statement [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_minorSection_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_minorSection_gaussian3), which supplies the archimedean gamma factors required by the converse theorem in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_minorSection_gaussian3_of_profile.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_minorSection_gaussian3_of_profile
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
    (hk₀ : k₀ = 0)
    (hodd : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P₂ = RealArchParam.principal u₁ a₁ u₂ a₂ → aR w₀ h₀ ≠ a₁)
    (par₀ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 0 1 : ℝ) : ℂ)) * ((M 1 2 : ℝ) : ℂ) -
        (((M 1 0 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ)) * ((M 0 2 : ℝ) : ℂ)) * gaussian3 M)

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
                ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
              = (((Real.pi : ℂ) * Complex.I * (-1 : ℂ) ^ c.val) * ρ) * (((twistedGammaR K (archOfParamR K P) uR aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod) := by sorry
