-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_torusPair_jacquetVector3_eq_integral_quasiChar_mul_torusIntegral_mul_godementMellin
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_torusPair_jacquetVector3_eq_integral_quasiChar_mul_torusIntegral_mul_godementMellin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/53da6b56-5fbe-5de3-913e-a80d89b83966
-- title:
--   Unfolding the archimedean torus pairing of the GL₃ Jacquet vector
-- statement:
--   The setting is the archimedean frame of the cubic converse-theorem argument; the binders fall into the following groups.
--
--   **Cubic field and twist.** $K$ is a number field whose ring of integers carries an integral $\mathcal O_{\mathbb Q}$-algebra structure, with $[K:\mathbb Q]=3$ (`_hdeg`); $\mu$ is a monoid homomorphism from the idele units of $K$ to $\mathbb C^\times$ which is an admissible twist (`_hμ`), i.e. trivial on principal ideles, continuous and of absolute value $1$ everywhere; and `_hns` asserts that no admissible twist $\eta$ of $\mathbb Q$ satisfies, for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and with $\eta$ unramified at the prime $p$ of $\mathcal O_{\mathbb Q}$ below $\mathfrak P$, the relation $\mu(\varpi_{\mathfrak P})=\eta(\varpi_p)^{f}$, where $\varpi$ denotes the uniformizer idele (`uniformizerIdele`) and $f$ is the inertia degree `inertiaDeg'` of $\mathfrak P$ over $p$.
--
--   **Archimedean parameters of $\mu$.** Functions $uR,aR$ on the real places and $uC,kC$ on the complex places of $K$, with values in $\mathbb C$, $\mathbb Z/2$, $\mathbb C$, $\mathbb Z$ respectively, and hypotheses `huR`, `huC` stating that at each real place $w$ the local archimedean component of $\mu$ is $x\mapsto \|x\|^{\mathrm{mult}_w\, uR(w)}(x/\|x\|)^{(aR(w))\cdot}$ (the exponent being the integer lift of $aR(w)\in\mathbb Z/2$), and likewise at each complex place $w$ with parameters $uC(w)$, $kC(w)$, in the sense of `IsArchCompAt`.
--
--   **The character $\omega$ of $\mathbb Q$.** A monoid homomorphism $\omega$ on the idele units of $\mathbb Q$, with `hω` a threefold conjunction: $\omega$ is an admissible twist; for every finite place $p$ of $\mathbb Q$ which is not a bad place for $(K,\mu)$ — i.e. $p$ is unramified in $K$ and $\mu$ is unramified at every prime of $K$ above $p$ — $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals $\mathrm{inducedE3}$ of the coefficient family $\mathfrak P\mapsto\mu(\varpi_{\mathfrak P})$ (that is, minus the degree-$3$ coefficient of the induced Euler polynomial) at $p$; and, for every choice of archimedean parameter data $(uR,aR,uC,kC)$ for $\mu$ as above and every real place $v$ of $\mathbb Q$, the archimedean component of $\omega$ at $v$ has parameters $\sum_w uR(w)+\sum_w 2\,uC(w)$ and $\sum_w (aR(w))\cdot+\sum_w (kC(w)+1)$, the sums being finsums over the real and complex places of $K$.
--
--   **Splitting of the infinite ideles.** A monoid homomorphism $E$ from the units of the infinite adeles of $\mathbb Q$ to the idele units, with `hE`: the infinite part of $E(u)$ is $u$ and its finite part is $1$.
--
--   **Normalisation of the additive character.** $a\in\mathbb Q$ with $a\neq 0$ and $a=-1$; a unit $a_\infty$ of the infinite adeles whose underlying element is the image of $a$; and an additive character $\psi_\infty$ of the infinite adeles of $\mathbb Q$ with $\psi_\infty(x)=\mathrm{psiArch}(a\,x)$ for all $x$.
--
--   **Measures.** Measurable and Borel structures on the infinite adeles of $\mathbb Q$ and on their unit group; an additive measure $\nu_{\mathrm{add}}$ equal to $|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the identification of the infinite adeles with the mixed space; and a Haar measure $\nu_{\mathrm{mul}}$ on the unit group.
--
--   **The $\mathrm{GL}_2$ archimedean datum over $\mathbb Q$.** A real archimedean parameter $P$ (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u_0,n)$ with $n\ge1$), subject to `_hP₁`: in the principal case $|\mathrm{Re}(u_1-u_2)|<1$. Data $kw:\mathbb Z/2\times\{\text{infinite places of }\mathbb Q\}\to\mathbb Z$, radial functions $Wr:\mathbb Z/2\times\{\text{places}\}\to(\mathbb C\to\mathbb C)$ and $WA:\mathbb Z/2\to(\mathrm{GL}_2(\mathbb R)\to\mathbb C)$ with the laws: `hkw1`, in the principal case $kw(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$; `hkw2`, in the discrete case $kw(\mathrm{par},w)=n+1$; `hWr1`, in the principal case with $a_1=a_2$ and $\mathrm{par}=a_1$, $Wr(\mathrm{par},w)(-t)=(-1)^{a_1}Wr(\mathrm{par},w)(t)$; `hWr2`, in the discrete case $Wr(\mathrm{par},w)(t)=0$ for $t<0$; `hWr3`, in the principal case with $a_1=a_2$ and $\mathrm{par}=a_1+1$, there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (Wr(\mathrm{par},w)(t)+(-1)^{a_1}Wr(\mathrm{par},w)(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}\,0\,a_1$ at $s$; `hWr4`, for every $b$ with $b=\mathrm{par}$ or $b=\mathrm{par}+P.\mathrm{centralSign}$, there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the same Mellin transform with $(-1)^{b}$ in place of $(-1)^{a_1}$ converges and equals the archimedean factor of $P.\mathrm{twist}\,0\,b$ at $s$. The function $WA(\mathrm{par})$ satisfies: `hWAN`, $WA(\mathrm{par})(u(x)h)=e^{-2\pi i a x}WA(\mathrm{par})(h)$ for the unipotent $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; `hWAZ`, $WA(\mathrm{par})(z\cdot h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}}WA(\mathrm{par})(h)$ for scalar matrices $z\in\mathbb R^\times$; `hWAK`, $WA(\mathrm{par})(h\kappa)=\mathrm{archWeightChar}_{\mathbb R}(kw(\mathrm{par},\mathrm{default}))(\kappa)\,WA(\mathrm{par})(h)$ for $\kappa$ in the row-isometry subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt`, $WA(\mathrm{par})(\mathrm{diag}(t,1))=Wr(\mathrm{par},\mathrm{default})(t)$ for $t\in\mathbb R^\times$; and `hWAc`, continuity of $WA(\mathrm{par})$. Finally an element $w_{0R}\in\mathrm{GL}_2(\mathbb R)$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   **The distinguished real place and the Levi parameter.** A real place $w_0$ of $K$ (with witness $h_0$) and a real archimedean parameter $P_2$ subject to `hP₂`: either $K$ has exactly the three real places $w_0,w_1,w_2$, pairwise distinct, and $P_2=\mathrm{principal}(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$; or $K$ has exactly the places $w_C$ (complex) and $w_0$, and either $kC(w_C)\neq0$ and $P_2=\mathrm{discrete}(uC(w_C),|kC(w_C)|)$, or $kC(w_C)=0$ and $P_2=\mathrm{principal}(uC(w_C),0,uC(w_C),1)$.
--
--   **The $\mathrm{GL}_2(\mathbb R)$ Whittaker datum.** $D$ is an `ArchDatumR P₂`: a function $D.W$ on real $2\times2$ matrices, smooth on the invertible locus, with the unipotent and central transformation laws, together with the zeta integrals, their archimedean-factor identity, functional equation, finite order and decay estimates packaged in that structure. In addition: an integer $k_0$ and `hDW`, $D.W(x\kappa)=\mathrm{archWeightChar}_{\mathbb R}(k_0)(\kappa)D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, $D$ is a Casimir eigenfunction, $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all $x$ with $\det x\neq0$; and `hDnz`, $D.W$ does not vanish identically on $\mathrm{GL}_2(\mathbb R)$.
--
--   **Schwartz datum and parity.** A function $S$ on real $2\times3$ matrices lying in `polyGauss3`, i.e. of the form (polynomial in the entries) times the Gaussian $\mathrm{gaussian3}$, and a parity $\mathrm{par}_0\in\mathbb Z/2$.
--
--   **Conclusion.** There exists $\sigma_u\in\mathbb R$ such that for every $s\in\mathbb C$ with $\mathrm{Re}\,s>\sigma_u$ the following identity of integrals with respect to Lebesgue measure holds. On the left, the iterated integral over $a_2\in(0,\infty)$ and $a_1\in\mathbb R$ of the integrand which vanishes unless $a_1\neq0$ and $0<a_2$, and which in that case, with $q=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}\in\mathrm{GL}_2(\mathbb R)$ (`upperUnit a₁ 0 a₂`), equals
--   $$WA(\mathrm{par}_0)(q)\cdot \mathrm{jacquetVector3}\,D\,(uR(w_0))\,(aR(w_0))\,a\,\psi_\infty\,S\bigl(\mathrm{archComponent3}(\iota(\mathrm{archRealGLAt}\,q))\bigr)\cdot |\det q|^{\,s-1/2}\cdot a_1^{-2},$$
--   where $\mathrm{archRealGLAt}$ transports $q$ to the adelic $\mathrm{GL}_2$ of $\mathbb Q$ at the unique infinite place, $\iota$ is the block embedding into adelic $\mathrm{GL}_3$ and $\mathrm{archComponent3}$ its infinite-adelic component. On the right, the integral over $e\in\mathbb R^{2\times2}$ (functions $\mathrm{Fin}\,2\to\mathrm{Fin}\,2\to\mathbb R$, regarded as matrices) of
--   $$\mathrm{quasiChar}(uR(w_0)+2,\,aR(w_0))(\det e)\cdot |\det e|^{-2}\cdot T(e,s)\cdot M(e,s),$$
--   where $\mathrm{quasiChar}(u,\alpha)(y)=|y|^{u}$ times $1$ if $\alpha=0$ and $\mathrm{sign}(y)$ otherwise,
--   $$T(e,s)=\int_{\mathbb R} Wr(\mathrm{par}_0,\mathrm{default})(t)\cdot D.W\bigl(\mathrm{diag}(a t,1)\cdot e^{-1}\bigr)\cdot |t|^{\,s-1/2}\cdot t^{-2}\,dt,$$
--   $$M(e,s)=\int_{0}^{\infty} y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\cdot \mathrm{godementInner3}\bigl(\psi_\infty\!\cdot\!(\,\cdot\,y)\bigr)(S)(e)(1)\,dy,$$
--   the additive character in $M$ being the multiplicative shift of $\psi_\infty$ by $\mathrm{ofReal}(y)$, and $\mathrm{godementInner3}\,\psi\,S\,h\,m=\int_{\mathbb R^2}S\bigl(h\cdot[\,m_{0\bullet}+v_0 m_{2\bullet};\,m_{1\bullet}+v_1 m_{2\bullet}\,]\bigr)\,\psi(\mathrm{ofReal}(-v_1))\,dv$, here with $h=e$ and $m$ the identity $3\times3$ matrix.
--
--   This is the archimedean unfolding step: the $\mathrm{GL}_2\times\mathrm{GL}_3$ torus pairing of the real Whittaker function $WA$ against the Jacquet vector attached to the Whittaker datum $D$ and the polynomial-times-Gaussian section $S$ is rewritten, in a right half-plane, as an integral over real $2\times2$ matrices of a one-dimensional torus integral of $D.W$ times a Godement-type Mellin transform of $S$. It is used by the two archimedean pair-row results that identify such pairings with gamma factors of the parameters $P$ and $P_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_torusPair_jacquetVector3_eq_integral_quasiChar_mul_torusIntegral_mul_godementMellin.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_torusPair_jacquetVector3_eq_integral_quasiChar_mul_torusIntegral_mul_godementMellin
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
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) (par₀ : ZMod 2) :
    ∃ σu : ℝ, ∀ s : ℂ, σu < s.re →
      (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                ((WA par₀ q * (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
        = ∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)) := by sorry
