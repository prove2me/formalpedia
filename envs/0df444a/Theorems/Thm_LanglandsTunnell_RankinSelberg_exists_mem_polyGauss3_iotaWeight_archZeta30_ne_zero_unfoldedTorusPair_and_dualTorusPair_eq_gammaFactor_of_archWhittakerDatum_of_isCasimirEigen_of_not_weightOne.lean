-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_not_weightOne
-- name    : LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_not_weightOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/66b3b482-9728-511c-bf69-2d079a5dc9f4
-- title:
--   Archimedean Rankin–Selberg pair outside weight-one GL₂ parameters
-- statement:
--   Setting. $K$ is a number field of degree $3$ over $\mathbb{Q}$ (hypothesis `_hdeg`), carrying an integral algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$, and $\mu\colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ is an admissible twist (`_hμ`): it is trivial on the image of $K^\times$, continuous, and all its values have modulus $1$. The hypothesis `_hns` states that $\mu$ is not of base-change shape: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and with $\eta$ unramified at the prime $p=\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ below it, $\mu$ of the uniformizer idele at $\mathfrak{P}$ equals $\eta$ of the uniformizer idele at $p$ raised to the inertia degree of $\mathfrak{P}$ over $p$. (Unramifiedness at $v$ means here that the local character is trivial on those units of the completion at $v$ whose value and inverse both lie in the valuation ring.)
--
--   Archimedean data of $\mu$. Functions $uR, aR$ on the real places and $uC, kC$ on the complex places of $K$ (with values in $\mathbb{C}$, $\mathbb{Z}/2$, $\mathbb{C}$, $\mathbb{Z}$ respectively) are given, and `huR`, `huC` assert that the archimedean local component of $\mu$ at each real place $w$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,uR(w)}\,(\iota_w(x)/\|x\|)^{(aR(w)).\mathrm{val}}$ and at each complex place $w$ is the analogous expression with exponents $uC(w)$ and $kC(w)$.
--
--   The character $\omega$ of $\mathbb{Q}$. The hypothesis `hω` has three clauses: $\omega$ is an admissible twist of $\mathbb{Q}$; for every prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ which is not a bad place for $(K,\mu)$ — that is, $p$ neither ramifies in $K$ nor is twist-ramified for $\mu$ — the character $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\text{uniformizer idele at }p)$ equals $-$ the degree-$3$ coefficient of the induced Euler polynomial of the coefficient system $\mathfrak{P}\mapsto \mu(\text{uniformizer idele at }\mathfrak{P})$ (zero at ramified $\mathfrak{P}$); and, for all archimedean data satisfying the two conditions of the previous paragraph, the archimedean component of $\omega$ at the real place of $\mathbb{Q}$ has exponent $\sum_w uR(w) + \sum_w 2\,uC(w)$ and weight $\sum_w (aR(w)).\mathrm{val} + \sum_w (kC(w)+1)$, the sums being over the real and complex places of $K$.
--
--   Idelic and measure-theoretic normalisations. $E$ is a monoid homomorphism from the units of the infinite adele ring of $\mathbb{Q}$ to the idele units, splitting the infinite part: `hE` says that the infinite part of $E(u)$ is $u$ and its finite part is $1$. The rational number $a$ satisfies $a\neq 0$ and $a=-1$ (`ha`, `ha1`); $aInf$ is an infinite idele unit whose underlying element is the image of $a$; $psiInf$ is the additive character $x\mapsto \psi_{\mathrm{arch}}(a\,x)$ of the infinite adele ring (`hpsiInf`). The measure $\nu_{\mathrm{add}}$ is $|a|^{1/2}$ times the push-forward of Lebesgue measure under the inverse of the identification of the infinite adele ring with the mixed space (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on the infinite idele units; the ambient measurable-space and Borel instances are the standard ones.
--
--   The $GL_2$ archimedean parameter and its Whittaker data. $P$ is a real archimedean parameter, i.e. either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ with $u_i\in\mathbb{C}$, $a_i\in\mathbb{Z}/2$, or $\mathrm{discrete}(u,k)$ with $k\ge 1$; `_hP₁` requires that if $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $|\mathrm{Re}(u_1-u_2)|<1$. Functions $kw$ (integer weights), $Wr$ (functions on $\mathbb{R}$) and $WA$ (functions on $GL_2(\mathbb{R})$), all indexed by a parity in $\mathbb{Z}/2$ and, for the first two, by an infinite place of $\mathbb{Q}$, are given, subject to: `hkw1`, for $P$ principal, $kw(\mathrm{par},w) = \mathrm{signShift}(a_1+\mathrm{par}) + \mathrm{signShift}(a_2+\mathrm{par})$, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$; `hkw2`, for $P=\mathrm{discrete}(u_0,n)$, $kw(\mathrm{par},w)=n+1$; `hWr1`, for $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1$, the parity law $Wr(\mathrm{par},w)(-t)=(-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w)(t)$; `hWr2`, for $P$ discrete, $Wr(\mathrm{par},w)$ vanishes on the negative reals; `hWr3`, for $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par}=a_1+1$, there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of $t\mapsto (Wr(\mathrm{par},w)(t)+(-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w)(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P$ twisted by $(0,a_1)$ at $s$; `hWr4`, for every parity $b$ with $b=\mathrm{par}$ or $b=\mathrm{par}+P.\mathrm{centralSign}$, there is $s_0$ such that for $\mathrm{Re}\,s>s_0$ the Mellin transform of the correspondingly symmetrised function converges and equals the archimedean factor of $P$ twisted by $(0,b)$ at $s$. The function $WA$ satisfies the Whittaker transformation laws `hWAN` (under the unipotent $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ on the left, by $\exp(-2\pi i a x)$), `hWAZ` (under a scalar $z\in\mathbb{R}^\times$, by $|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}$), `hWAK` (right translation by $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb{R})$ multiplies $WA(\mathrm{par},\cdot)$ by the weight character `archWeightCharℝ (kw par default)` of $\kappa$), `hWAt` ($WA(\mathrm{par},\mathrm{diag}(t,1)) = Wr(\mathrm{par},\text{default})(t)$ for $t\in\mathbb{R}^\times$) and `hWAc` (continuity in the group variable). Finally $w_{0R}\in GL_2(\mathbb{R})$ is the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   The induced $GL_2$ parameter $P_2$ and its datum. $w_0$ is a real place of $K$ and $P_2$ a real archimedean parameter for which `hP₂` offers two alternatives: either $K$ has exactly the three pairwise distinct real places $w_0,w_1,w_2$ and $P_2=\mathrm{principal}(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$; or $K$ has exactly the places $w_0$ and one complex place $w_C$, and then either $kC(w_C)\neq 0$ and $P_2=\mathrm{discrete}(uC(w_C),|kC(w_C)|)$, or $kC(w_C)=0$ and $P_2=\mathrm{principal}(uC(w_C),0,uC(w_C),1)$. Further, $D$ is an archimedean Whittaker datum of parameter $P_2$ (a function $W$ on $2\times 2$ real matrices, smooth on the invertible locus, with the unipotent and central transformation laws, an entire zeta function together with integrability, the identification of its zeta integral as the archimedean factor of $P_2$ twisted by $(u,a)$ times that entire function, the functional equation with the epsilon factor of the twist, finite order in vertical strips, and decay at $0$ and $\infty$; these clauses are summarised here), and $k_0$ is an integer such that: `hDW`, $D.W(x\kappa) = \mathrm{archWeightChar}_{\mathbb{R}}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, $D$ is a Casimir eigenfunction, $\mathrm{matrixCasimir}(D.W)(x) = P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for every invertible $x$; `hDnz`, $D.W$ does not vanish identically on $GL_2(\mathbb{R})$; `hk₀min`, if $P_2=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, and if $P_2=\mathrm{discrete}(u,m)$ then $k_0=m+1$.
--
--   The restricting hypothesis. `hPnw1` excludes the weight-one principal case for $P$: there are no $u_1,u_2,a_1,a_2$ with $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ and $a_1\neq a_2$. Thus $P$ is either a discrete-series parameter or a principal parameter with equal parities.
--
--   Conclusion. There exist a parity $\mathrm{par}_0\in\mathbb{Z}/2$ and a polynomial-Gaussian Schwartz datum $S\in$ `polyGauss3` — a function on $2\times 3$ real matrices of the form $M\mapsto p(\text{entries of }M)\cdot \mathrm{gaussian3}(M)$ for some complex multivariate polynomial $p$ — such that, writing $J$ for the Jacquet vector `jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) a psiInf S` on $GL_3$ of the infinite adeles of $\mathbb{Q}$ (the quasicharacter $\mathrm{quasiChar}(uR(w_0)+1, aR(w_0))$ of the determinant of the real matrix of $g$ times the integral over $2\times 2$ real matrices of `jacquetIntegrand3`), and writing $\iota(\kappa)$ for the archimedean component of the image of $\kappa\in GL_2(\mathbb{R})$ under the embedding at the real place of $\mathbb{Q}$ into the adelic $GL_2$ followed by `iota` into the adelic $GL_3$, the following three assertions hold.
--
--   (i) Weight law: for every $\kappa$ in `rowIsometrySubgroup₀ ℝ` and every $g\in GL_3$ of the infinite adeles, $J(g\,\iota(\kappa)) = \mathrm{archWeightChar}_{\mathbb{R}}(kw(\mathrm{par}_0,\text{default}))(\kappa)^{-1}\,J(g)$.
--
--   (ii) Non-vanishing of the archimedean $GL_3\times GL_1$ zeta integral: there exist an admissible twist $\sigma$ of $\mathbb{Q}$ and $s\in\mathbb{C}$ with $\mathrm{archZeta}_{30}(\nu_{\mathrm{mul}}, J, \sigma\circ E, s)(1)\neq 0$, that is, $\int J(\mathrm{diag}(\alpha,1,1))\,\sigma(E\alpha)\,\|\alpha\|^{s-1}\,\mathrm{d}\nu_{\mathrm{mul}}(\alpha)\neq 0$, the integral being over the infinite idele units.
--
--   (iii) There exist $\sigma_a\in\mathbb{R}$ and $e\in\mathbb{C}$ with $e\neq 0$ such that both of the following identities hold for every $s$ with $\mathrm{Re}\,s>\sigma_a$. (In the first identity the matrix of integration and the constant are both written `e` in the Lean text; here the matrix is denoted $h$.)
--
--   First (the unfolded primal torus pair): the integral over $2\times 2$ real matrices $h$ of
--   $$\mathrm{quasiChar}(uR(w_0)+2, aR(w_0))(\det h)\cdot |\det h|^{-2}\cdot\Big(\int_{\mathbb{R}} Wr(\mathrm{par}_0,\text{default})(t)\,D.W\big(\mathrm{diag}(a t,1)\,h^{-1}\big)\,|t|^{\,s-\frac12}\,t^{-2}\,\mathrm{d}t\Big)\cdot\Big(\int_0^{\infty} y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\,\mathrm{godementInner3}\big(psiInf\cdot\chi_y, S, h, 1\big)\,\mathrm{d}y\Big)$$
--   equals $e$ times the product of $\Gamma_{\mathbb{R}}(s+\tfrac12+x)$ over the multiset $\mathrm{twistedGamma}_{\mathbb{R}}(K, w\mapsto P, uR, aR)$ times the product of $\Gamma_{\mathbb{C}}(s+\tfrac12+x)$ over the multiset $\mathrm{twistedGamma}_{\mathbb{C}}(K, w\mapsto P, w\mapsto P.\mathrm{baseChange}, uR, aR, uC, kC)$; here $\chi_y$ denotes the multiplicative shift of $psiInf$ by the real number $y$ viewed in the infinite adele ring, and $\mathrm{godementInner3}(\psi,S,h,m)$ is $\int_{\mathbb{R}^2} S\big(h\cdot(\text{rows } m_0+v_0m_2,\ m_1+v_1m_2)\big)\,\psi(-v_1)\,\mathrm{d}v$ with $m$ the $3\times 3$ identity.
--
--   Second (the dual torus pair): the iterated integral over $a_2\in(0,\infty)$ and $a_1\in\mathbb{R}$ of the integrand which, when $a_1\neq 0$ and $a_2>0$, equals, with $q=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}\in GL_2(\mathbb{R})$,
--   $$|\det q|\cdot WA\big(\mathrm{par}_0,\ w_{0R}\,{}^{t}(q^{-1})\big)\cdot \big(\mathrm{dualWhittakerFn3}\,J\big)(\iota(q))\cdot |\det q|^{\,s-\frac12}\cdot a_1^{-2},$$
--   and vanishes otherwise, equals
--   $$\Big(\mathrm{archRootNumber}(K, w\mapsto P, w\mapsto P.\mathrm{baseChange}, uR, aR, uC, kC)\cdot(-1)^{P.\mathrm{centralSign}.\mathrm{val}}\cdot(-1)^{r_2}\Big)\,e$$
--   times the product of $\Gamma_{\mathbb{R}}(s+\tfrac12+x)$ over $\mathrm{twistedGamma}_{\mathbb{R}}(K, w\mapsto P.\mathrm{dual}, -uR, aR)$ times the product of $\Gamma_{\mathbb{C}}(s+\tfrac12+x)$ over $\mathrm{twistedGamma}_{\mathbb{C}}(K, w\mapsto P.\mathrm{dual}, w\mapsto (P.\mathrm{baseChange}).\mathrm{dual}, -uR, aR, -uC, -kC)$, where $r_2$ is the number of complex places of $K$, $\mathrm{dualWhittakerFn3}\,J$ is $g\mapsto J(\mathrm{longWeyl3}\cdot{}^{t}(g^{-1}))$, $\mathrm{archRootNumber}$ is the product over the real places of $K$ of the epsilon factors of $P$ twisted by $(uR(w),aR(w))$ with the product over the complex places of the epsilon factors of $P.\mathrm{baseChange}$ twisted by $(uC(w),kC(w))$, and the twisted gamma multisets are the sums over the places of $K$ of the $\Gamma_{\mathbb{R}}$- and $\Gamma_{\mathbb{C}}$-shift multisets of the corresponding twisted parameters.
--
--   This is the archimedean Rankin–Selberg step in the cubic-induction input to the converse theorem: it produces, for a cubic field $K$ and a non-base-change idele class character $\mu$, a polynomial-Gaussian section whose archimedean $GL_3\times GL_2$ zeta pair is a nonzero multiple of the expected product of $\Gamma_{\mathbb{R}}$- and $\Gamma_{\mathbb{C}}$-factors, together with the matching identity for the dual pair and the root number. It is the instance of that statement in which the $GL_2$ archimedean parameter $P$ is not principal of weight one (so discrete series, or principal with equal parities), and it is combined with the complementary weight-one case in [`LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen`](thm.html#LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_not_weightOne.lean

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
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open LanglandsTunnell.RankinSelberg
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_not_weightOne
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
    (hPnw1 : ¬ ∃ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ ∧ a₁ ≠ a₂) :
    ∃ (par₀ : ZMod 2), ∃ S ∈ polyGauss3,
        (∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
            (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (g * (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) κ))))
              = ((archWeightCharℝ (kw par₀ default) ⟨κ, hκ⟩ : ℂ))⁻¹ * (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) g) ∧
        (∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (σ.comp E) s 1 ≠ 0) ∧
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
