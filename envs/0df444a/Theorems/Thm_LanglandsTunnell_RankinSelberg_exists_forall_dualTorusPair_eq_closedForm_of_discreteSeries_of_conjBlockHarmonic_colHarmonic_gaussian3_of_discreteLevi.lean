-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_dualTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_discreteLevi
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_discreteLevi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/a8db2d6a-0342-524c-a6e9-90af0be5b3e8
-- title:
--   Closed form of the dual torus integral, discrete Levi branch
-- statement:
--   The setting is a cubic field and a non-descended idele class character of it, together with archimedean Whittaker data on $\mathrm{GL}_2(\mathbb{R})$ and a degree-$m$ flat section on $2\times 3$ real matrices; the assertion is an explicit evaluation, for $\operatorname{Re} s$ large, of the dual torus integral occurring after unfolding, in the branch where both archimedean parameters are of discrete type.
--
--   **Field and twist data.** $K$ is a number field with an $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_K$ that is integral, and `_hdeg` asserts $[K:\mathbb{Q}]=3$. A character $\mu\colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ is given, with `_hμ` requiring that $\mu$ be an admissible twist, i.e. trivial on $K^\times$, continuous, and of absolute value $1$ everywhere. The hypothesis `_hns` asserts that there is **no** admissible twist $\eta$ of $\mathbb{Q}$ such that, for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose trace $\mathfrak{p}=\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ is unramified for $\eta$, the value of $\mu$ on the uniformizer idele at $\mathfrak{P}$ equals the value of $\eta$ on the uniformizer idele at $\mathfrak{p}$ raised to the residue degree `inertiaDeg'` of $\mathfrak{P}$ over $\mathfrak{p}$.
--
--   **Archimedean components of $\mu$.** Functions $u_R, a_R$ on the real places and $u_C, k_C$ on the complex places of $K$ are given, with values in $\mathbb{C}$, $\mathbb{Z}/2$, $\mathbb{C}$, $\mathbb{Z}$ respectively; `huR` and `huC` assert that at each real place $w$ the local component of $\mu$ is $x \mapsto \|x\|^{\mathrm{mult}(w)\,u_R(w)}(x/\|x\|)^{a_R(w)}$ (the exponent being the canonical lift of $a_R(w)\in\mathbb{Z}/2$ to $\{0,1\}$), and at each complex place $w$ it is $x\mapsto \|x\|^{\mathrm{mult}(w)\,u_C(w)}(x/\|x\|)^{k_C(w)}$.
--
--   **The descended character $\omega$.** A character $\omega$ of the idele class group of $\mathbb{Q}$ is given, and `hω` has three clauses: $\omega$ is an admissible twist; at every prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ which is not bad for $(K,\mu)$ — bad meaning either ramified in $K$ or carrying a prime of $K$ above it at which $\mu$ is ramified — $\omega$ is unramified and its Euler coefficient equals $\mathrm{inducedE3}$, the negated degree-$3$ coefficient of the induced Euler polynomial, evaluated on the unramified coefficients of $\mu$; and, for any data $u_R,a_R,u_C,k_C$ satisfying the same archimedean conditions as above, the component of $\omega$ at the real place of $\mathbb{Q}$ has exponent $\sum_{w \text{ real}} u_R(w) + \sum_{w \text{ complex}} 2u_C(w)$ and sign exponent $\sum_{w \text{ real}} a_R(w) + \sum_{w \text{ complex}}(k_C(w)+1)$ (finprod-style sums).
--
--   **Splitting of ideles and additive character.** $E$ is a homomorphism from the infinite ideles of $\mathbb{Q}$ to the ideles, with `hE` asserting that the infinite part of $E(u)$ is $u$ and the finite part is $1$. A rational $a\neq 0$ with $a=-1$ is fixed (`ha`, `ha1`), $a_{\infty}$ is an infinite idele unit whose underlying element is the image of $a$ (`haInf`), and $\psi_{\infty}$ is the additive character $x \mapsto \psi_{\mathrm{arch}}(a x)$ (`hpsiInf`).
--
--   **Measure normalisations.** Measurable and Borel structures on the infinite adele ring of $\mathbb{Q}$ and on its units are assumed; $\nu_{\mathrm{add}}$ is the measure $|a|^{1/2}$ times the pushforward of Lebesgue measure along the inverse of the identification of the infinite adele ring with the mixed space (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on the unit group.
--
--   **The $\mathrm{GL}_2(\mathbb{R})$ profile.** $P$ is a real archimedean parameter (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u,k)$ with $k\ge 1$), and `_hP₁` requires $|\operatorname{Re}(u_1-u_2)|<1$ whenever $P$ is principal (a condition void once `hPdisc` below is imposed). Data $k_w\colon \mathbb{Z}/2\times \mathrm{InfinitePlace}(\mathbb{Q})\to\mathbb{Z}$, $W_r\colon \mathbb{Z}/2\times\mathrm{InfinitePlace}(\mathbb{Q})\times\mathbb{R}\to\mathbb{C}$ and $W_A\colon\mathbb{Z}/2\times \mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$ are subject to the following hypotheses, for every parity $\mathrm{par}$ and every real place $w$ of $\mathbb{Q}$: `hkw1`, if $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ then $k_w(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ as complex numbers, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$; `hkw2`, if $P=\mathrm{discrete}(u_0,n_0)$ then $k_w(\mathrm{par},w)=n_0+1$; `hWr1`, in the principal case with $a_2=a_1$ and $\mathrm{par}=a_1$, $W_r(\mathrm{par},w,-t)=(-1)^{a_1}W_r(\mathrm{par},w,t)$ for all real $t$; `hWr2`, in the discrete case $W_r(\mathrm{par},w,t)=0$ for $t<0$; `hWr3`, in the principal case with $a_2=a_1$ and $\mathrm{par}=a_1+1$ there is an abscissa beyond which the Mellin transform of $t\mapsto (W_r(\mathrm{par},w,t)+(-1)^{a_1}W_r(\mathrm{par},w,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}\,0\,a_1$ at $s$; `hWr4`, for $b$ equal to $\mathrm{par}$ or to $\mathrm{par}+P.\mathrm{centralSign}$, the same symmetrised Mellin transform converges for $\operatorname{Re} s$ large and equals the archimedean factor of $P.\mathrm{twist}\,0\,b$ at $s$. The function $W_A$ satisfies: `hWAN`, the unipotent law $W_A(\mathrm{par}, n(x)h)=e^{-2\pi i a x}W_A(\mathrm{par},h)$; `hWAZ`, the central law $W_A(\mathrm{par}, z h) = |z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}}W_A(\mathrm{par},h)$ for scalar $z$; `hWAK`, right equivariance $W_A(\mathrm{par}, h\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(k_w(\mathrm{par},\ast))(\kappa)\,W_A(\mathrm{par},h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`, the weight being taken at the default infinite place of $\mathbb{Q}$; `hWAt`, the restriction $W_A(\mathrm{par},\mathrm{diag}(t,1))=W_r(\mathrm{par},\ast,t)$ for $t\in\mathbb{R}^\times$; and `hWAc`, continuity of $W_A(\mathrm{par},\cdot)$. Finally $w_{0R}\in \mathrm{GL}_2(\mathbb{R})$ is the antidiagonal involution $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀R`).
--
--   **The Levi datum.** A real place $w_0$ of $K$ is fixed, and $P_2$ is a real archimedean parameter subject to `hP₂`: either $K$ has exactly three infinite places $w_0,w_1,w_2$, pairwise distinct and all real, with $P_2=\mathrm{principal}(u_R(w_1),a_R(w_1),u_R(w_2),a_R(w_2))$; or $K$ has exactly the two infinite places $w_C$ (complex) and $w_0$, and then either $k_C(w_C)\neq 0$ and $P_2=\mathrm{discrete}(u_C(w_C),|k_C(w_C)|)$, or $k_C(w_C)=0$ and $P_2=\mathrm{principal}(u_C(w_C),0,u_C(w_C),1)$. A datum $D$ of type `ArchDatumR P₂` is given (a function $D.W$ on real $2\times2$ matrices, smooth on the invertible locus, with the unipotent and central transformation laws for $P_2$, an entire zeta function with the stated integral representation, functional equation, finite order and decay properties), together with an integer $k_0$ and: `hDW`, right equivariance $D.W(x\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(\kappa)D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, the Casimir eigenvalue equation $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ at every $x$ of nonzero determinant; `hDnz`, $D.W$ is not identically zero; and `hk₀min`, minimality of $k_0$: if $P_2$ is principal with signs $a_1,a_2$ then $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, while if $P_2=\mathrm{discrete}(u,m_0)$ then $k_0=m_0+1$.
--
--   **Discrete-series specialisation and flat section.** `hPdisc` fixes $P=\mathrm{discrete}(u_P,n_P)$ with $n_P\ge1$, and $m=n_P+1$ (`hm`). A natural number $n$ and a real $\varepsilon'$ satisfy `hcol`: either $\varepsilon'=-1$ and $n=k_0-m$, or $\varepsilon'=1$ and $n=m-k_0$. A parity $\mathrm{par}_0\in\mathbb{Z}/2$ is fixed. The section $S$ on $2\times3$ real matrices is given by `hS` as
--   $$S(M)=\bigl((M_{00}-iM_{10})-i(M_{01}-iM_{11})\bigr)^m\,\bigl(M_{02}+\varepsilon' i M_{12}\bigr)^n\,\exp\Bigl(-\pi\sum_{i,b}M_{ib}^2\Bigr).$$
--   The profile $W_r$ at parity $\mathrm{par}_0$ and the default place is prescribed explicitly: $W_r(\mathrm{par}_0,\ast,t)=2\,t^{u_P+n_P/2+1}e^{-2\pi t}$ for $t>0$ (`hWpos`) and $=0$ for $t<0$ (`hWneg`). The Levi branch is restricted by `hP₂eq`: $P_2=\mathrm{discrete}(\mu,k)$ with $k\ge 1$, where $\mu\in\mathbb{C}$ (the name $\mu$ is reused here for this complex parameter) and $\rho\in\mathbb{C}$; and $D.W$ is prescribed on the torus by `hDpos`, $D.W(\mathrm{diag}(\tau,1))=\rho\cdot 2\,\tau^{\mu+k/2+1}e^{-2\pi\tau}$ for $\tau>0$, and `hDneg`, $D.W(\mathrm{diag}(-\tau,1))=0$ for $\tau>0$.
--
--   **Conclusion.** There exists a real abscissa $\sigma_a$ such that for every $s\in\mathbb{C}$ with $\sigma_a<\operatorname{Re} s$ the iterated integral
--   $$\int_{a_2>0}\int_{a_1\in\mathbb{R}} |\det q|\;W_A\bigl(\mathrm{par}_0, w_{0R}\cdot {}^{t}q^{-1}\bigr)\; \widetilde{J}\bigl(\iota(q)_{\infty}\bigr)\;|\det q|^{s-1/2}\;a_1^{-2}\,da_1\,da_2,$$
--   taken with respect to Lebesgue measure and with the integrand set to $0$ unless $a_1\neq0$ and $a_2>0$, equals
--   $$\pi\, i^{m}\,(-1)^{m+n+a_R(w_0)}\,2^{m}\;\Gamma_{\mathbb{R}}\bigl(2s-P.\mathrm{centralExponent}-P_2.\mathrm{centralExponent}+n+1\bigr)\;(2\pi)^{-(s-u_R(w_0)-u_P+m/2)}\,\Gamma\bigl(s-u_R(w_0)-u_P+\tfrac m2\bigr)\;\Bigl(2\rho\,\Gamma\bigl(s-u_P-\mu+\tfrac{m+k}{2}\bigr)(4\pi)^{-(s-u_P-\mu+(m+k)/2)}\Bigr).$$
--   Here $q=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$ is the Siegel coordinate matrix [`AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂`](def/AutomorphicForm_SiegelCoordinates.html#L126), ${}^{t}q^{-1}$ is [`RSCarrier.transposeInv q`](def/LanglandsTunnell_RSCarrier.html#L31), the exponent $a_R(w_0)$ in the sign is the canonical lift to $\{0,1\}$, and $\widetilde{J}$ denotes the dual Whittaker function $g\mapsto J(\mathrm{longWeyl}_3\cdot {}^{t}g^{-1})$ of the Jacquet vector $J=\mathrm{jacquetVector3}\,D\,u_R(w_0)\,a_R(w_0)\,a\,\psi_\infty\,S$, evaluated at the archimedean component of the image of $q$ under the real-place embedding $\mathrm{GL}_2(\mathbb{R})\to\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ followed by the block inclusion $\iota$ into $\mathrm{GL}_3$. Since both $P$ and $P_2$ are of discrete type, the two central exponents occurring in the $\Gamma_{\mathbb{R}}$-argument are $2u_P$ and $2\mu$.
--
--   This is the archimedean computation of the dual half of the unfolded Rankin–Selberg torus integral for the $\mathrm{GL}_3\times\mathrm{GL}_2$ pairing used in the converse-theorem step towards the Langlands–Tunnell theorem, in the branch where the $\mathrm{GL}_2$ parameter and the Levi parameter are both discrete, with explicit one-sided Whittaker profiles and the degree-$m$ Gaussian flat section. It is obtained from the reduction of the dual torus pair to a constant multiple of a torus integral of $D.W$, and feeds the assembly statement `exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_oneComplex_discreteLevi`, where the primal and dual closed forms are compared to extract the archimedean gamma factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_dualTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_discreteLevi.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_discreteLevi
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
    (μ : ℂ) (k : ℕ) (hk : 1 ≤ k) (hP₂eq : P₂ = RealArchParam.discrete μ k hk) (ρ : ℂ)
    (hDpos : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne τ) = ρ * ((2 : ℂ) * ((τ : ℂ) ^ (μ + (k : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * τ)) : ℂ))))
    (hDneg : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0) :
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
              (ρ * (2 : ℂ) * Complex.Gamma (s - uP - μ + ((m : ℂ) + (k : ℂ)) / 2) * (4 * (Real.pi : ℂ)) ^ (-(s - uP - μ + ((m : ℂ) + (k : ℂ)) / 2))) := by sorry
