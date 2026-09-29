-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/4bc056c4-a292-5cca-988a-e5c928c53087
-- title:
--   Even principal torus-pair identities for a weight-zero Gaussian section
-- statement:
--   Data. $K$ is a number field of degree $3$ over $\mathbb{Q}$ (hypothesis `_hdeg`), equipped with an $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_K$ for which $\mathcal{O}_K$ is integral over $\mathcal{O}_{\mathbb{Q}}$. Further, $\mu$ is a homomorphism from the ideles of $K$ to $\mathbb{C}^\times$ and $\omega$ one for $\mathbb{Q}$; $P$ and $P_2$ are real archimedean parameters, i.e. elements of `RealArchParam`, each either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb{C}$, $a_i\in\mathbb{Z}/2$, or $\mathrm{discrete}(u,k)$ with $k\ge 1$; $D$ is an archimedean Whittaker datum of type $P_2$ (a term of `ArchDatumR P₂`, carrying a function $D.W$ on $M_2(\mathbb{R})$ that is smooth on the invertible locus, transforms by the standard character under left multiplication by unipotents and by the central character of $P_2$ under scalars, and comes with an entire zeta function satisfying a functional equation and prescribed growth and decay); and $S$ is a complex-valued function on $M_{2\times 3}(\mathbb{R})$.
--
--   Character hypotheses. `_hμ` asserts that $\mu$ is an admissible twist of $K$: trivial on the principal ideles, continuous and of absolute value $1$. `_hns` asserts a non-descent condition: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose restriction $p=\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ is a place where $\eta$ is unramified, the value of $\mu$ on a uniformiser idele at $\mathfrak{P}$ equals the value of $\eta$ on a uniformiser idele at $p$ raised to the inertia degree of $\mathfrak{P}$ over $p$. The archimedean profile of $\mu$ is recorded by $u_{\mathbb{R}},a_{\mathbb{R}}$ on the real places and $u_{\mathbb{C}},k_{\mathbb{C}}$ on the complex places: `huR` and `huC` state that at each real place $w$ the local component of $\mu$ is $x\mapsto \lVert x\rVert^{\,\mathrm{mult}(w)\,u_{\mathbb{R}}(w)}\,(x/\lVert x\rVert)^{a_{\mathbb{R}}(w).\mathrm{val}}$, and at each complex place $w$ it is $x\mapsto\lVert x\rVert^{\,\mathrm{mult}(w)\,u_{\mathbb{C}}(w)}(x/\lVert x\rVert)^{k_{\mathbb{C}}(w)}$. The hypothesis `hω` has three clauses: $\omega$ is an admissible twist of $\mathbb{Q}$; at every finite place $p$ of $\mathbb{Q}$ which is not a bad place for $(K,\mu)$ (that is, $p$ is unramified in $K$ and $\mu$ is not twist-ramified above $p$), $\omega$ is unramified and its Euler coefficient at $p$ equals $-$the degree-$3$ coefficient of the induced Euler polynomial built from the unramified coefficients of $\mu$; and for every admissible archimedean profile $(u_{\mathbb{R}},a_{\mathbb{R}},u_{\mathbb{C}},k_{\mathbb{C}})$ of $\mu$ and every real place $v$ of $\mathbb{Q}$, the archimedean component of $\omega$ at $v$ has exponent $\sum_w u_{\mathbb{R}}(w)+\sum_w 2u_{\mathbb{C}}(w)$ and integer parameter $\sum_w a_{\mathbb{R}}(w).\mathrm{val}+\sum_w (k_{\mathbb{C}}(w)+1)$.
--
--   Adelic and measure-theoretic bookkeeping. $E$ is a homomorphism from the units of the infinite adeles of $\mathbb{Q}$ to the ideles with `hE`: the infinite part of $E(u)$ is $u$ and the finite part is $1$. The rational number $a$ is non-zero and equal to $-1$; $a_\infty$ is a unit of the infinite adeles whose underlying adele is the image of $a$; $\psi_\infty$ is the additive character $x\mapsto \psi_{\mathrm{arch}}(a x)$ for the standard archimedean character $\psi_{\mathrm{arch}}$ of $\mathbb{Q}$. The additive measure $\nu_{\mathrm{add}}$ is $|a|^{1/2}$ times the transport of Lebesgue measure on the mixed space along the inverse of the ring equivalence $\mathbb{A}_{\mathbb{Q},\infty}\cong$ mixed space, and $\nu_{\mathrm{mul}}$ is a Haar measure on the unit group.
--
--   The $\mathrm{GL}_2$ archimedean profile. `_hP₁` requires $|\mathrm{Re}(u_1-u_2)|<1$ whenever $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$. Attached to $P$ are a weight function $k_w:\mathbb{Z}/2\times\{\text{places of }\mathbb{Q}\}\to\mathbb{Z}$, radial functions $W_r$ and a function $W_A$ on $\mathrm{GL}_2(\mathbb{R})$, indexed by a parity in $\mathbb{Z}/2$, subject to: `hkw1`, $k_w(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ in the principal case, where $\mathrm{signShift}(a)$ is $0$ for $a=0$ and $1$ otherwise; `hkw2`, $k_w(\mathrm{par},w)=n+1$ if $P=\mathrm{discrete}(u_0,n)$; `hWr1`, if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1$ then $W_r(\mathrm{par},w,-t)=(-1)^{a_1.\mathrm{val}}W_r(\mathrm{par},w,t)$; `hWr2`, in the discrete case $W_r(\mathrm{par},w,t)=0$ for $t<0$; `hWr3`, if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1+1$ then for $\mathrm{Re}\,s$ large the Mellin transform of $t\mapsto (W_r(\mathrm{par},w,t)+(-1)^{a_1.\mathrm{val}}W_r(\mathrm{par},w,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean $\Gamma$-factor of $P$ twisted by $(0,a_1)$; `hWr4`, for each $b'$ equal to $\mathrm{par}$ or to $\mathrm{par}+P.\mathrm{centralSign}$ the analogous Mellin transform with $(-1)^{b'.\mathrm{val}}$ converges for $\mathrm{Re}\,s$ large and equals the archimedean $\Gamma$-factor of $P$ twisted by $(0,b')$. The function $W_A$ satisfies: `hWAN`, $W_A(\mathrm{par},u(x)h)=e^{-2\pi i a x}W_A(\mathrm{par},h)$ for unipotent $u(x)$; `hWAZ`, $W_A(\mathrm{par},zh)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}W_A(\mathrm{par},h)$ for scalar matrices $z$; `hWAK`, right equivariance under the row-isometry subgroup of $\mathrm{GL}_2(\mathbb{R})$ by the weight character of weight $k_w(\mathrm{par},\cdot)$ at the real place of $\mathbb{Q}$; `hWAt`, $W_A(\mathrm{par},\mathrm{diag}(t,1))=W_r(\mathrm{par},\cdot,t)$; and `hWAc`, continuity. Finally $w_{0R}\in\mathrm{GL}_2(\mathbb{R})$ is the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   The Levi datum. $w_0$ is a real place of $K$, and `hP₂` fixes the signature of $K$ together with $P_2$: either there are two further real places $w_1\neq w_2$, distinct from $w_0$, exhausting the places of $K$, and $P_2=\mathrm{principal}(u_{\mathbb{R}}(w_1),a_{\mathbb{R}}(w_1),u_{\mathbb{R}}(w_2),a_{\mathbb{R}}(w_2))$; or there is a complex place $w_C$ such that every infinite place of $K$ is $w_C$ or $w_0$, and either $k_{\mathbb{C}}(w_C)\neq 0$ and $P_2=\mathrm{discrete}(u_{\mathbb{C}}(w_C),|k_{\mathbb{C}}(w_C)|)$, or $k_{\mathbb{C}}(w_C)=0$ and $P_2=\mathrm{principal}(u_{\mathbb{C}}(w_C),0,u_{\mathbb{C}}(w_C),1)$. The datum $D$ is of weight $k_0\in\mathbb{Z}$ in the sense of `hDW`: $D.W(x r)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(r)\,D.W(x)$ for $r$ in the row-isometry subgroup; `hDE` states that $D$ is a Casimir eigenfunction, $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all $x$ with $\det x\neq 0$, where the eigenvalue is $\tfrac14-\big(\tfrac{u_1-u_2}{2}\big)^2$ in the principal case and $\tfrac{1-k^2}{4}$ in the discrete case; `hDnz` states $D.W\not\equiv 0$; and `hk₀min` requires $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2 \pmod 2$ when $P_2=\mathrm{principal}(u_1,a_1,u_2,a_2)$, and $k_0=m+1$ when $P_2=\mathrm{discrete}(u,m)$.
--
--   Even principal type and the section. The hypothesis `hPev` puts $P$ in even principal form, $P=\mathrm{principal}(\nu_1,b,\nu_2,b)$ with equal sign characters; `hLevi` requires that if $k_0=0$ and $P_2=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $a_1=b$. The natural number $n$ satisfies $n=k_0$, and $\delta\in\{0,1\}$ satisfies $\delta\equiv a_{\mathbb{R}}(w_0)+b$ in $\mathbb{Z}/2$. The section is
--   $$S(M)=(M_{00}M_{11}-M_{01}M_{10})^{\delta}\,\big(M_{02}-iM_{12}\big)^{n}\,\exp\Big(-\pi\sum_{i<2}\sum_{b<3}M_{ib}^2\Big).$$
--
--   Conclusion. There exist $\sigma_a\in\mathbb{R}$ and $e\in\mathbb{C}$ such that the following three assertions hold.
--
--   First, $e\neq 0$.
--
--   Second, for every $s$ with $\mathrm{Re}\,s>\sigma_a$,
--   $$\int_{M_2(\mathbb{R})}\chi_{u_{\mathbb{R}}(w_0)+2,\,a_{\mathbb{R}}(w_0)}(\det\varepsilon)\,|\det\varepsilon|^{-2}\,I_1(\varepsilon,s)\,I_2(\varepsilon,s)\,d\varepsilon\;=\;e\cdot\Gamma_P(s),$$
--   where $\chi_{u,a}(y)=|y|^{u}$ times $\mathrm{sign}(y)$ when $a\neq 0$ and times $1$ when $a=0$; $I_1(\varepsilon,s)=\int_{\mathbb{R}}W_r(b,\cdot,t)\,D.W\big(\mathrm{diag}(at,1)\,\varepsilon^{-1}\big)\,|t|^{s-1/2}\,t^{-2}\,dt$; $I_2(\varepsilon,s)=\int_0^\infty y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\,\mathrm{godementInner3}\big(\psi_\infty^{(y)},S,\varepsilon,1\big)\,dy$ with $\psi_\infty^{(y)}$ the shift of $\psi_\infty$ by the infinite adele attached to $y$, and $\mathrm{godementInner3}(\psi,S,h,m)=\int_{\mathbb{R}^2}S\big(h\cdot[\,b\mapsto m_{0b}+v_0m_{2b};\,b\mapsto m_{1b}+v_1m_{2b}\,]\big)\psi(-v_1)\,dv$; and $\Gamma_P(s)$ is the product of $\Gamma_{\mathbb{R}}(s+\tfrac12+x)$ over the multiset $\mathrm{twistedGammaR}$ of real shifts of the constant family $w\mapsto P$ twisted by $(u_{\mathbb{R}},a_{\mathbb{R}})$, times the product of $\Gamma_{\mathbb{C}}(s+\tfrac12+x)$ over the multiset $\mathrm{twistedGammaC}$ assembled from the constant families $w\mapsto P$ at the real places and $w\mapsto P.\mathrm{baseChange}$ at the complex places, twisted by $(u_{\mathbb{R}},a_{\mathbb{R}})$ and $(u_{\mathbb{C}},k_{\mathbb{C}})$ respectively.
--
--   Third, for every $s$ with $\mathrm{Re}\,s>\sigma_a$,
--   $$\int_0^\infty\!\!\int_{\mathbb{R}}\Big[\,|\det q|\,W_A\big(b,\;w_{0R}\,(q^{-1})^{\mathsf T}\big)\cdot \widetilde{J}(q)\cdot|\det q|^{\,s-1/2}\cdot a_1^{-2}\,\Big]\,da_1\,da_2\;=\;\big(\epsilon_\infty\cdot(-1)^{P.\mathrm{centralSign}.\mathrm{val}}\cdot(-1)^{\#\{\text{complex places of }K\}}\cdot e\big)\cdot\Gamma_{P^{\vee}}(s),$$
--   the integrand being understood as $0$ unless $a_1\neq 0$ and $a_2>0$, in which case $q$ denotes the upper-triangular element $\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$ of $\mathrm{GL}_2(\mathbb{R})$. Here $\widetilde{J}(q)$ is the dual Whittaker function $g\mapsto J(\mathrm{longWeyl}_3\cdot (g^{-1})^{\mathsf T})$ of the Jacquet vector $J=\mathrm{jacquetVector3}\,D\,u_{\mathbb{R}}(w_0)\,a_{\mathbb{R}}(w_0)\,a\,\psi_\infty\,S$, evaluated at the archimedean component of the image of $q$ under the embedding of $\mathrm{GL}_2(\mathbb{R})$ at the real place of $\mathbb{Q}$ followed by the inclusion of $\mathrm{GL}_2$ into adelic $\mathrm{GL}_3$; $\mathrm{jacquetVector3}$ is $g\mapsto \chi_{u_{\mathbb{R}}(w_0)+1,\,a_{\mathbb{R}}(w_0)}(\det g_\infty)\int_{M_2(\mathbb{R})}\mathrm{jacquetIntegrand3}\,(\cdots)\,d\varepsilon$. The constant $\epsilon_\infty=\mathrm{archRootNumber}$ is the product over the real places of $K$ of the epsilon factors of $P$ twisted by $(u_{\mathbb{R}},a_{\mathbb{R}})$ times the product over the complex places of the epsilon factors of $P.\mathrm{baseChange}$ twisted by $(u_{\mathbb{C}},k_{\mathbb{C}})$. Finally $\Gamma_{P^{\vee}}(s)$ is the product of $\Gamma_{\mathbb{R}}(s+\tfrac12+x)$ over $\mathrm{twistedGammaR}$ for the dual parameter family $w\mapsto P^{\vee}$ with exponents $-u_{\mathbb{R}}$ and signs $a_{\mathbb{R}}$, times the product of $\Gamma_{\mathbb{C}}(s+\tfrac12+x)$ over $\mathrm{twistedGammaC}$ for the dual families $w\mapsto P^{\vee}$ and $w\mapsto (P.\mathrm{baseChange})^{\vee}$ with exponents $-u_{\mathbb{R}},-u_{\mathbb{C}}$, signs $a_{\mathbb{R}}$ and weights $-k_{\mathbb{C}}$, where duality negates the exponents and keeps the signs and weights.
--
--   This is the archimedean Rankin–Selberg step for the $\mathrm{GL}_3\times\mathrm{GL}_2$ pairing attached to a cubic field $K$ and an idele class character $\mu$ of $K$, in the case where the $\mathrm{GL}_2$ parameter at the real place of $\mathbb{Q}$ is of even principal type: for the explicit det-power times column-harmonic Gaussian section it evaluates both the unfolded torus-pair integral and its dual against the long Weyl element, the two sides differing exactly by the archimedean root number, the sign $(-1)^{P.\mathrm{centralSign}.\mathrm{val}}$, the sign of the number of complex places, and the passage to dual $\Gamma$-shifts. It supplies the even-principal branch of the archimedean input to the $\mathrm{GL}_3$ converse theorem used for the cubic base change, and is cited by the statement covering parameters that are not of weight-one principal type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3.lean

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
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3
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
    (hLevi : k₀ = 0 → ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P₂ = RealArchParam.principal u₁ a₁ u₂ a₂ → a₁ = b)
    (n : ℕ) (hn : (n : ℤ) = k₀)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = aR w₀ h₀ + b)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M) :
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
