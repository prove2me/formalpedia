-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_discrete_profile
-- name    : LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_discrete_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/1906f765-17c5-5ffe-9b76-75e7b16ee800
-- title:
--   Dual torus pair identity, discrete Levi branch
-- statement:
--   The setting is a number field $K$ of degree $3$ over $\mathbb{Q}$ (the hypothesis `_hdeg` asserts $\operatorname{finrank}_{\mathbb{Q}} K = 3$), with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra.
--
--   **The character $\mu$ and its non-descent.** A homomorphism $\mu : (\mathbb{A}_K)^{\times} \to \mathbb{C}^{\times}$ is given, which by `_hμ` is an admissible twist, i.e. trivial on the principal ideles $K^{\times}$, continuous, and of absolute value $1$ everywhere. The hypothesis `_hns` asserts that $\mu$ does not descend in the following Euler-coefficient sense: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified (its local character is trivial on the local units) and at whose underlying prime $p = \mathfrak{P} \cap \mathcal{O}_{\mathbb{Q}}$ the character $\eta$ is unramified, one has $\mu(\varpi_{\mathfrak{P}}) = \eta(\varpi_p)^{f(\mathfrak{P}/p)}$, where $\varpi$ denotes the uniformizer idele at the place in question and $f$ the inertia degree.
--
--   **Archimedean data of $\mu$.** Families $uR, aR$ (over the real places of $K$, with values in $\mathbb{C}$ and $\mathbb{Z}/2$) and $uC, kC$ (over the complex places, with values in $\mathbb{C}$ and $\mathbb{Z}$) are given; `huR` and `huC` assert that at each real place $w$ the archimedean local component of $\mu$ is $x \mapsto \|x\|^{\mathrm{mult}(w)\,uR_w}(\iota_w(x)/\|x\|)^{(aR_w)\text{.val}}$, and at each complex place $w$ it is the analogous expression with exponents $uC_w$ and $kC_w$.
--
--   **The induced character $\omega$ on $\mathbb{Q}$.** A homomorphism $\omega : (\mathbb{A}_{\mathbb{Q}})^{\times} \to \mathbb{C}^{\times}$ is given, and `hω` is a three-clause conjunction: $\omega$ is an admissible twist; at every prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ which is not a bad place for $(K,\mu)$ (that is, $p$ is unramified in $K$ and $\mu$ is not twist-ramified above $p$), $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals $-$ the degree-$3$ coefficient of the induced Euler polynomial formed from the coefficients $\mathfrak{P} \mapsto \mu(\varpi_{\mathfrak{P}})$ (taken to be $0$ at ramified $\mathfrak{P}$); and, for any families $uR, aR, uC, kC$ satisfying the two archimedean-component conditions above, at every real place $v$ of $\mathbb{Q}$ the archimedean component of $\omega$ has exponents $\sum_{w \text{ real}} uR_w + \sum_{w \text{ complex}} 2\,uC_w$ and $\sum_{w \text{ real}} (aR_w)\text{.val} + \sum_{w \text{ complex}} (kC_w + 1)$ (the sums being finprod-style sums over the places).
--
--   **Adelic and measure-theoretic normalisations.** A monoid homomorphism $E$ from the infinite idele units of $\mathbb{Q}$ to the full idele units is given with `hE`: $E$ is a section of the infinite-part map whose finite part is trivial. A rational number $a$ is given with $a \neq 0$ and $a = -1$; a unit $aInf$ of the infinite adeles with underlying element the image of $a$; and an additive character $psiInf$ of the infinite adeles with $psiInf(x) = \psi_{\mathrm{arch}}(a x)$ for the standard archimedean character $\psi_{\mathrm{arch}}$. Measurable and Borel structures on the infinite adeles and their units are fixed, $\nu_{\mathrm{add}}$ is the transport of Lebesgue measure under the inverse of the identification of the infinite adeles with the mixed space, scaled by $|a|^{1/2}$, and $\nu_{\mathrm{mul}}$ is a Haar measure on the units.
--
--   **The $\mathrm{GL}_2(\mathbb{R})$ Whittaker family.** A real archimedean parameter $P$ is given, with `_hP₁`: if $P$ is principal with data $u_1, a_1, u_2, a_2$ then $|\mathrm{Re}(u_1 - u_2)| < 1$. Families $kw$ (integral weights), $Wr$ (functions on $\mathbb{R}$) and $WA$ (functions on $\mathrm{GL}_2(\mathbb{R})$), all indexed by a parity $par \in \mathbb{Z}/2$ and, for the first two, by a real place of $\mathbb{Q}$, are given, subject to: weight normalisations `hkw1` ($kw$ equals $\mathrm{signShift}(a_1+par) + \mathrm{signShift}(a_2+par)$ in the principal case, where $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$) and `hkw2` ($kw = n+1$ in the discrete case with lowest weight $n$); the parity law `hWr1` ($Wr_{par}(-t) = (-1)^{a_1.\mathrm{val}} Wr_{par}(t)$ when $P$ is principal with both signs equal to $a_1$ and $par = a_1$); the support law `hWr2` ($Wr_{par}$ vanishes on $t<0$ in the discrete case); two Mellin identities, `hWr3` (for $P$ principal with both signs $a_1$ and $par = a_1+1$, the Mellin transform of $t \mapsto (Wr_{par}(t) + (-1)^{a_1.\mathrm{val}}Wr_{par}(-t))/t$ converges in some right half-plane and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}\,0\,a_1$) and `hWr4` (for every $par$ and every $b$ with $b = par$ or $b = par + P.\mathrm{centralSign}$, the same Mellin transform converges in some right half-plane and equals the archimedean factor of $P.\mathrm{twist}\,0\,b$); and the equivariance properties of $WA$: `hWAN` (unipotent: $WA_{par}(n(x)h) = e^{-2\pi i a x}WA_{par}(h)$), `hWAZ` (central: $WA_{par}(zI\cdot h) = |z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}WA_{par}(h)$), `hWAK` (right transformation under `rowIsometrySubgroup₀ ℝ` by the weight character `archWeightCharℝ` of weight $kw_{par}$ at the default real place), `hWAt` ($WA_{par}(\mathrm{diagOne}\,t) = Wr_{par}(t)$) and `hWAc` (continuity of each $WA_{par}$). An element $w_{0R} \in \mathrm{GL}_2(\mathbb{R})$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ is fixed.
--
--   **The distinguished real place and the Levi datum.** A real place $w_0$ of $K$ is fixed, together with a real archimedean parameter $P_2$ and the place-configuration hypothesis `hP₂`: either $K$ has exactly three real places $w_0, w_1, w_2$ (pairwise distinct and exhausting the infinite places) and $P_2 = \mathrm{principal}\,(uR_{w_1})(aR_{w_1})(uR_{w_2})(aR_{w_2})$, or $K$ has one complex place $w_C$ and $w_0$ exhausting the infinite places, and either $kC_{w_C} \neq 0$ and $P_2 = \mathrm{discrete}\,(uC_{w_C})\,|kC_{w_C}|$, or $kC_{w_C} = 0$ and $P_2 = \mathrm{principal}\,(uC_{w_C})\,0\,(uC_{w_C})\,1$. An archimedean datum $D$ of type $P_2$ is given (a Whittaker function $W$ on $2\times 2$ real matrices with the smoothness, unipotent, central, zeta-integral, functional-equation, finite-order and decay properties of `ArchDatumR`), together with an integer $k_0$ and: `hDW`, right equivariance of $D.W$ under `rowIsometrySubgroup₀ ℝ` by `archWeightCharℝ` of weight $k_0$; `hDE`, the Casimir eigenvalue equation $\mathrm{matrixCasimir}(D.W) = P_2.\mathrm{laplaceEigenvalue}\cdot D.W$ on invertible matrices; `hDnz`, non-vanishing of $D.W$ at some point; and `hk₀min`, which requires $k_0 \in \{0,1\}$ with $k_0 \equiv a_1 + a_2 \pmod 2$ in the principal case for $P_2$, and $k_0 = m+1$ in the discrete case with lowest weight $m$.
--
--   **Even type, parity bookkeeping and the Schwartz seed.** Complex numbers $\nu_1, \nu_2$ and $b \in \mathbb{Z}/2$ are given with $P = \mathrm{principal}\,\nu_1\,b\,\nu_2\,b$ (even type: the two signs of $P$ coincide), together with `hLevi` (if $k_0 = 0$ and $P_2$ is principal with first sign $a_1$, then $a_1 = b$), a natural number $n$ with $(n : \mathbb{Z}) = k_0$, and $\delta \in \{0,1\}$ with $\delta \equiv aR_{w_0} + b \pmod 2$. The function $S$ on $2\times 3$ real matrices is $S(M) = (M_{00}M_{11} - M_{01}M_{10})^{\delta}\,(M_{02} - i\,M_{12})^{n}\,\exp\!\big(-\pi\sum_{i,b} M_{ib}^2\big)$: a power of the leading $2\times 2$ minor times a column-harmonic factor of degree $n$ times the standard Gaussian.
--
--   **The discrete profile.** Finally, $u \in \mathbb{C}$ and $m \geq 1$ are given with $P_2 = \mathrm{discrete}\,u\,m$ and $k_0 = m+1$ (so the branch of `hP₂` in force is the one with a single complex place and $kC_{w_C} \neq 0$), and $\rho \in \mathbb{C}$ with `hρ`: for $\tau > 0$ one has $D.W(\mathrm{diagOne}\,\tau) = \rho\cdot 2\,\tau^{u + m/2 + 1}e^{-2\pi\tau}$, and $D.W(\mathrm{diagOne}(-\tau)) = 0$.
--
--   **Conclusion.** There exists $\sigma_a \in \mathbb{R}$ such that for every $s \in \mathbb{C}$ with $\mathrm{Re}\,s > \sigma_a$ the iterated integral
--   $$\int_{a_2 > 0}\int_{a_1 \in \mathbb{R}} \Big[|\det q|\; WA_b\big(w_{0R}\cdot {}^{t}q^{-1}\big)\cdot \mathcal{J}\big(\mathrm{longWeyl}_3\cdot {}^{t}\tilde q^{-1}\big)\Big]\,|\det q|^{\,s-1/2}\,a_1^{-2}$$
--   equals
--   $$\Big(\varepsilon_{\infty}\cdot(-1)^{P.\mathrm{centralSign}.\mathrm{val}}\cdot(-1)^{\#\{\text{complex places of }K\}}\Big)\cdot\Big((-1)^{b.\mathrm{val}}\tfrac{\pi}{2}\,\rho\Big)\cdot\Gamma\text{-product},$$
--   where the integrand is taken to be $0$ unless $a_1 \neq 0$ and $a_2 > 0$; in that case $q = \begin{pmatrix}a_1&0\\0&a_2\end{pmatrix} \in \mathrm{GL}_2(\mathbb{R})$, ${}^{t}q^{-1}$ is [`RSCarrier.transposeInv q`](def/LanglandsTunnell_RSCarrier.html#L31), and $\mathcal{J}$ is the Jacquet vector `jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) a psiInf S`, evaluated by `dualWhittakerFn3` (that is, at $\mathrm{longWeyl}_3$ times the transpose-inverse of its argument) at the archimedean component of the image in $\mathrm{GL}_3$, under `iota`, of the adelic $\mathrm{GL}_2$-element obtained by placing $q$ at the real place of $\mathbb{Q}$. On the right, $\varepsilon_{\infty}$ is `archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC`, i.e. the product over the real places $w$ of the epsilon factor of $P$ twisted by $(uR_w, aR_w)$ times the product over the complex places $w$ of the epsilon factor of the base change $P.\mathrm{baseChange}$ twisted by $(uC_w, kC_w)$; and the $\Gamma$-product is the product of $x \mapsto \Gamma_{\mathbb{R}}(s + 1/2 + x)$ over the multiset `twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR` times the product of $x \mapsto \Gamma_{\mathbb{C}}(s + 1/2 + x)$ over the multiset `twistedGammaC K` formed from the duals of $P$ and of $P.\mathrm{baseChange}$ and the data $(-uR, aR, -uC, -kC)$.
--
--   This is the dual half, in the discrete-series branch for the Levi datum, of the archimedean Rankin–Selberg torus-pair computation for the cubic induction $\mathrm{GL}_1(K) \rightsquigarrow \mathrm{GL}_3(\mathbb{Q})$: the unfolded torus integral against the dual Whittaker function is evaluated as the archimedean root number, corrected by the two explicit signs, times the constant $(-1)^{b}\pi\rho/2$ and the dual twisted $\Gamma$-factor. It is used by [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3), which assembles the primal and dual halves into the archimedean input of the converse theorem for the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_discrete_profile.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_discrete_profile
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
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)

    (u : ℂ) (m : ℕ) (hm : 1 ≤ m) (hP₂eq : P₂ = RealArchParam.discrete u m hm) (hk₀ : k₀ = (m : ℤ) + 1)
    (ρ : ℂ)
    (hρ : (∀ τ : ℝ, 0 < τ →
        D.W (ArchR.diagOne τ) = ρ * ((2 : ℂ) * ((τ : ℂ) ^ (u + (m : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * τ)) : ℂ)))) ∧
      (∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0)) :
    ∃ σa : ℝ, (∀ s : ℂ, σa < s.re →
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA b (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = ((archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val * (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card) * (((-1 : ℂ) ^ b.val * ((Real.pi : ℂ) / 2)) * ρ)) * (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
                    (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod)) := by sorry
