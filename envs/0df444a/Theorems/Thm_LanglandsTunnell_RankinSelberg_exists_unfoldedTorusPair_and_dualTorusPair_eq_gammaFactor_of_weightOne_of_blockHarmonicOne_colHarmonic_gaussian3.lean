-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/05f27bda-61cd-5851-add1-815dc5ab6cd3
-- title:
--   Weight-one unfolded torus-pair identities with Γ-factors
-- statement:
--   The data are the following. A cubic field: a number field $K$ with $[K:\mathbb{Q}]=3$, together with an algebra structure making $\mathcal{O}_K$ integral over $\mathcal{O}_{\mathbb{Q}}$. A character: a homomorphism $\mu:(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ which is an admissible twist, i.e. trivial on the principal ideles $K^\times$, continuous and unitary. The non-descent hypothesis `_hns` asserts that there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose contraction $p=\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ is unramified for $\eta$ one has $\mu(\varpi_{\mathfrak{P}})=\eta(\varpi_p)^{f(\mathfrak{P}/p)}$, the exponent being the inertia degree; here $\varpi$ denotes the uniformizer idele at the place in question. Archimedean exponents: functions $uR,aR$ on the real places and $uC,kC$ on the complex places of $K$, with values in $\mathbb{C}$, $\mathbb{Z}/2$, $\mathbb{C}$, $\mathbb{Z}$ respectively, such that (hypotheses `huR`, `huC`) the local component of $\mu$ at a real place $w$ is $x\mapsto \|x\|^{m_w u_R(w)}(x/\|x\|)^{a_R(w)}$ and at a complex place $w$ is $x\mapsto \|x\|^{m_w u_C(w)}(x/\|x\|)^{k_C(w)}$, in the sense of the predicate `IsArchCompAt`.
--
--   A character of $\mathbb{Q}$: a homomorphism $\omega:(\mathbb{A}_{\mathbb{Q}})^\times\to\mathbb{C}^\times$ subject to the three clauses of `hω`: $\omega$ is an admissible twist; at every finite place $p$ of $\mathbb{Q}$ which is not a bad place for $(K,\mu)$ (that is, $p$ is neither ramified in $K$ nor twist-ramified for $\mu$, the predicate `IsBadPlace`), $\omega$ is unramified and its Euler coefficient $\omega(\varpi_p)$ equals $-$(coefficient of $X^3$ in the induced Euler polynomial of the coefficient system $\mathfrak{P}\mapsto\mu(\varpi_{\mathfrak{P}})$, the latter set to $0$ at ramified $\mathfrak{P}$), i.e. `inducedE3 ℚ (inducedCoeff K μ) p`; and, for every choice of archimedean exponents satisfying the two compatibilities above, the component of $\omega$ at the real place $v$ of $\mathbb{Q}$ has exponent $\sum_{w\text{ real}}u_R(w)+\sum_{w\text{ complex}}2u_C(w)$ and sign exponent $\sum_{w\text{ real}}a_R(w)+\sum_{w\text{ complex}}(k_C(w)+1)$. A splitting $E:(\mathbb{A}_{\mathbb{Q},\infty})^\times\to(\mathbb{A}_{\mathbb{Q}})^\times$ with `hE`: the infinite part of $E(u)$ is $u$ and its finite part is $1$. An additive parameter: $a\in\mathbb{Q}$ with $a\neq0$ and $a=-1$, a unit $a_\infty$ of the infinite adele ring with image $a$, and an additive character $\psi_\infty$ on $\mathbb{A}_{\mathbb{Q},\infty}$ with $\psi_\infty(x)=\psi_{\mathrm{arch}}(a x)$ for the standard archimedean character. Measures: measurable and Borel structures on $\mathbb{A}_{\mathbb{Q},\infty}$ and on its unit group, an additive measure $\nu_{\mathrm{add}}$ equal to $|a|^{1/2}$ times the transport of Lebesgue measure along the mixed-space identification, and a Haar measure $\nu_{\mathrm{mul}}$ on the units.
--
--   The $\mathrm{GL}_2$ archimedean package. A real archimedean parameter $P$ (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u,k)$ with $k\ge1$), subject to `_hP₁`: in the principal case $|\mathrm{Re}(u_1-u_2)|<1$. Weights $kw:\mathbb{Z}/2\times\{\text{infinite places of }\mathbb{Q}\}\to\mathbb{Z}$, radial functions $Wr$ indexed by a parity and an infinite place, and functions $WA:\mathbb{Z}/2\to\mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$. The weight hypotheses read: `hkw1`, in the principal case $kw(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ (where $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$), and `hkw2`, in the discrete case $kw(\mathrm{par},w)=n+1$. The radial hypotheses read: `hWr1`, if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1$ then $Wr(\mathrm{par},w)(-t)=(-1)^{a_1}Wr(\mathrm{par},w)(t)$; `hWr2`, in the discrete case $Wr(\mathrm{par},w)$ vanishes on $t<0$; `hWr3`, if $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1+1$ then for $\mathrm{Re}\,s$ large the Mellin transform of $t\mapsto (Wr(\mathrm{par},w)(t)+(-1)^{a_1}Wr(\mathrm{par},w)(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P$ twisted by $(0,a_1)$ at $s$; `hWr4`, for every parity and every $b$ equal to $\mathrm{par}$ or to $\mathrm{par}+\mathrm{centralSign}(P)$, the analogous symmetrised Mellin transform converges for $\mathrm{Re}\,s$ large and equals the archimedean factor of $P$ twisted by $(0,b)$ at $s$. The group-theoretic hypotheses on $WA$ read: `hWAN`, $WA(\mathrm{par})(u(x)h)=e^{-2\pi i a x}WA(\mathrm{par})(h)$ for unipotent $u(x)$; `hWAZ`, $WA(\mathrm{par})(z\cdot h)=|z|^{\mathrm{centralExponent}(P)+1}(z/|z|)^{\mathrm{centralSign}(P)}WA(\mathrm{par})(h)$ for scalar $z\in\mathbb{R}^\times$; `hWAK`, right equivariance under the row-isometry subgroup $\mathrm{rowIsometrySubgroup}_0(\mathbb{R})$ by the weight character $\mathrm{archWeightChar}_{\mathbb{R}}$ of weight $kw(\mathrm{par},\ast)$ at the place of $\mathbb{Q}$; `hWAt`, $WA(\mathrm{par})(\mathrm{diag}(t,1))=Wr(\mathrm{par},\ast)(t)$ for $t\in\mathbb{R}^\times$; and `hWAc`, continuity of each $WA(\mathrm{par})$. Finally $w_{0R}\in\mathrm{GL}_2(\mathbb{R})$ is the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   The Levi datum. A real place $w_0$ of $K$ and a real archimedean parameter $P_2$ such that (`hP₂`) either $K$ has exactly three infinite places $w_0,w_1,w_2$, pairwise distinct, and $P_2=\mathrm{principal}(u_R(w_1),a_R(w_1),u_R(w_2),a_R(w_2))$, or $K$ has exactly the two infinite places $w_C$ (complex) and $w_0$, and then either $k_C(w_C)\neq0$ and $P_2=\mathrm{discrete}(u_C(w_C),|k_C(w_C)|)$, or $k_C(w_C)=0$ and $P_2=\mathrm{principal}(u_C(w_C),0,u_C(w_C),1)$. An archimedean Whittaker datum $D$ for $P_2$ (a function $W$ on $2\times2$ real matrices, smooth on the invertible locus, with unipotent and central transformation laws, together with the entire completed zeta function, its functional equation with the $\epsilon$-factor of $P_2$, finite order, and the decay estimates packaged in `ArchDatumR`), an integer $k_0$, and the hypotheses: `hDW`, $D.W$ transforms on the right under $\mathrm{rowIsometrySubgroup}_0(\mathbb{R})$ by $\mathrm{archWeightChar}_{\mathbb{R}}(k_0)$; `hDE`, $D$ is a Casimir eigenfunction, $\mathrm{matrixCasimir}(D.W)(x)=\mathrm{laplaceEigenvalue}(P_2)\,D.W(x)$ for all $x$ with $\det x\neq0$; `hDnz`, $D.W$ does not vanish identically on $\mathrm{GL}_2(\mathbb{R})$; `hk₀min`, in the principal case $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, and in the discrete case $k_0=m+1$.
--
--   The weight-one branch: `hPw1` requires $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $a_1\neq a_2$; `hk₀` requires $k_0=0$; `heven` requires $a_R(w_0)=a_1$ whenever $P_2=\mathrm{principal}(u_1,a_1,u_2,a_2)$. A parity $\mathrm{par}_0\in\mathbb{Z}/2$ is given, and the section $S$ on $2\times3$ real matrices is the explicit one
--   $$S(M)=\bigl((M_{00}+iM_{10})-i(M_{01}+iM_{11})\bigr)\,(M_{02}-iM_{12})^1\,e^{-\pi\sum_{i,b}M_{ib}^2}.$$
--
--   Conclusion: there exist an abscissa $\sigma_a\in\mathbb{R}$ and a non-zero complex constant (named `e` in the statement; written $c$ here, the letter `e` being reused for the matrix variable of integration in the first identity) such that both of the following hold.
--
--   First, for every $s$ with $\mathrm{Re}\,s>\sigma_a$, the integral over $e\in M_2(\mathbb{R})$ (Lebesgue measure) of
--   $$\chi_{u_R(w_0)+2,\,a_R(w_0)}(\det e)\,|\det e|^{-2}\Bigl(\int_{\mathbb{R}}Wr(\mathrm{par}_0,\ast)(t)\,D.W\bigl(\mathrm{diag}(at,1)\,e^{-1}\bigr)|t|^{s-1/2}\,t^{-2}\,dt\Bigr)\Bigl(\int_0^{\infty}y^{\,\mathrm{centralExponent}(P)+\mathrm{centralExponent}(P_2)+2s}\,\mathrm{godementInner3}\bigl(\psi_\infty(\,\cdot\,y),S,e,1\bigr)\,dy\Bigr)$$
--   equals $c$ times the product of $\Gamma_{\mathbb{R}}(s+\tfrac12+x)$ over the multiset $\mathrm{twistedGammaR}$ and of $\Gamma_{\mathbb{C}}(s+\tfrac12+x)$ over the multiset $\mathrm{twistedGammaC}$ formed from the constant parameter functions $w\mapsto P$ at real places and $w\mapsto P^{\mathrm{bc}}$ at complex places, twisted by $(u_R,a_R)$ and $(u_C,k_C)$. Here $\chi_{u,a}(y)=|y|^{u}$ times $\mathrm{sign}(y)$ if $a\neq0$, and $\mathrm{godementInner3}(\psi,S,h,m)=\int_{v\in\mathbb{R}^2}S\bigl(h\cdot(\text{rows }m_{0\ast}+v_0m_{2\ast},\,m_{1\ast}+v_1m_{2\ast})\bigr)\psi(-v_1)\,dv$, evaluated at $m=1$ and with $\psi=\psi_\infty$ shifted by the real scalar $y$.
--
--   Second, for every $s$ with $\mathrm{Re}\,s>\sigma_a$, the iterated integral over $a_2\in(0,\infty)$ and $a_1\in\mathbb{R}$ of the integrand which, when $a_1\neq0$ and $a_2>0$, is formed from $q=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}\in\mathrm{GL}_2(\mathbb{R})$ as
--   $$|\det q|\,WA(\mathrm{par}_0)\bigl(w_{0R}\cdot{}^{t}q^{-1}\bigr)\cdot \bigl(\mathrm{dualWhittakerFn3}\,\mathcal{J}\bigr)\bigl(\text{archimedean component of }\iota(q_{\text{real place}})\bigr)\cdot|\det q|^{\,s-1/2}\cdot a_1^{-2},$$
--   and is $0$ otherwise, equals
--   $$\bigl(\mathrm{archRootNumber}\cdot(-1)^{\mathrm{centralSign}(P)}\cdot(-1)^{\#\{\text{complex places of }K\}}\cdot c\bigr)$$
--   times the product of $\Gamma_{\mathbb{R}}(s+\tfrac12+x)$ and $\Gamma_{\mathbb{C}}(s+\tfrac12+x)$ over the analogous multisets formed from the dual parameters $w\mapsto P^{\vee}$, $w\mapsto (P^{\mathrm{bc}})^{\vee}$, twisted by $(-u_R,a_R)$ and $(-u_C,-k_C)$. Here $\mathcal{J}$ is the Jacquet vector $\mathrm{jacquetVector3}\,D\,u_R(w_0)\,a_R(w_0)\,a\,\psi_\infty\,S$, whose value at $g\in\mathrm{GL}_3$ is $\chi_{u_R(w_0)+1,a_R(w_0)}(\det g_{\mathbb{R}})\int_{M_2(\mathbb{R})}\mathrm{jacquetIntegrand3}$, $\mathrm{dualWhittakerFn3}\,W(g)=W(w_3\cdot{}^{t}g^{-1})$ with $w_3$ the long Weyl element of $\mathrm{GL}_3$, the matrix $q$ is embedded at the real place of $\mathbb{Q}$ into the adelic $\mathrm{GL}_2$, mapped by the cubic-induction embedding $\iota$ into the adelic $\mathrm{GL}_3$ and then projected to its archimedean component, and $\mathrm{archRootNumber}$ is the product over the real places of $K$ of the $\epsilon$-factors of $P$ twisted by $(u_R,a_R)$ times the product over the complex places of the $\epsilon$-factors of $P^{\mathrm{bc}}$ twisted by $(u_C,k_C)$. The two identities share the same constant $c$ and the same abscissa $\sigma_a$.
--
--   This is the archimedean Rankin–Selberg computation for the cubic induction in the weight-one principal case with minimal Levi weight $k_0=0$: for the explicit block-harmonic Gaussian section $S$ it evaluates both the unfolded torus integral and its dual (Weyl-translated, transpose-inverse) counterpart as one and the same non-zero constant times the twisted $\Gamma$-factors of $\Pi(\mu)\otimes\pi$, respectively of the contragredients, with the archimedean root number in front on the dual side. It is the clause used by `exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen`, which supplies the archimedean input to the converse-theorem argument for the cubic base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_weightOne_of_blockHarmonicOne_colHarmonic_gaussian3
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
    (heven : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P₂ = RealArchParam.principal u₁ a₁ u₂ a₂ → aR w₀ h₀ = a₁)
    (par₀ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ))) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ 1) * gaussian3 M) :
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
