-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_profile
-- name    : LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/49d88c55-c6ce-5f58-b488-44e5d24bd6e8
-- title:
--   Dual torus pair with explicit constant 2π(-1)ᵇρ
-- statement:
--   The setting is a number field $K$ of degree $3$ over $\mathbb{Q}$ (hypothesis `_hdeg`), equipped with an integral algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$, together with a character $\mu$ of the idele group of $K$ with values in $\mathbb{C}^\times$.
--
--   **Character hypotheses.** `_hμ` asserts that $\mu$ is an admissible twist, i.e. it is trivial on the principal ideles $K^\times$, continuous, and of absolute value $1$ at every idele. `_hns` asserts the non-existence of an admissible twist $\eta$ of $\mathbb{Q}$ such that for every $\mathfrak{P}$ of `HeightOneSpectrum (𝓞 K)` at which $\mu$ is unramified (trivial on local units) and $\eta$ is unramified at the prime $p$ of $\mathbb{Q}$ below $\mathfrak{P}$, the value $\mu$ takes on a uniformiser idele at $\mathfrak{P}$ equals the value of $\eta$ on a uniformiser idele at $p$ raised to the inertia degree $f(\mathfrak{P}/p)$; so $\mu$ is not a base change of a character of $\mathbb{Q}$ in this Euler-coefficient sense.
--
--   **Archimedean data for $\mu$.** Functions $uR, aR$ on the real places and $uC, kC$ on the complex places of $K$, with $aR$ valued in $\mathbb{Z}/2$ and $kC$ in $\mathbb{Z}$; `huR` and `huC` assert `IsArchCompAt`, namely that for each place $w$ and each $x$ in the units of $w$'s completion the archimedean local component of $\mu$ at $w$ is $\|x\|^{\mathrm{mult}(w)\,u}\,(x/\|x\|)^{a}$, with $(u,a)=(uR\,w,(aR\,w).\mathrm{val})$ at real places and $(u,a)=(uC\,w,kC\,w)$ at complex places.
--
--   **The auxiliary character $\omega$ of $\mathbb{Q}$.** The hypothesis `hω` has three clauses: $\omega$ is an admissible twist of $\mathbb{Q}$; at every prime $p$ of $\mathbb{Q}$ which is not a bad place for $(K,\mu)$ (the predicate `IsBadPlace`, a disjunction of ramification in $K$ and twist-ramification of $\mu$ above $p$), $\omega$ is unramified at $p$ and its Euler coefficient at $p$ equals `inducedE3 ℚ (inducedCoeff K μ) p`, i.e. minus the degree-$3$ coefficient of the induced Euler polynomial built from the unramified values of $\mu$; and, for any quadruple of archimedean data satisfying the two `IsArchCompAt` conditions above, the archimedean component of $\omega$ at the real place $v$ of $\mathbb{Q}$ has exponent $\sum_{w\ \mathrm{real}} uR\,w + \sum_{w\ \mathrm{complex}} 2\,uC\,w$ and sign exponent $\sum_{w\ \mathrm{real}} (aR\,w).\mathrm{val} + \sum_{w\ \mathrm{complex}} (kC\,w+1)$ (finite sums).
--
--   **Adelic frame.** A monoid map $E$ from the units of the infinite adeles of $\mathbb{Q}$ to the ideles of $\mathbb{Q}$ with `hE`: the infinite part of $E(u)$ is $u$ and the finite part is $1$. A rational $a$ with $a\neq 0$ and $a=-1$; an infinite idele $aInf$ whose underlying infinite adele is the image of $a$; an additive character $psiInf$ on the infinite adeles given by $psiInf(x)=\psi_{\mathrm{arch}}(a x)$ for the standard archimedean character. Measurable and Borel structures on the infinite adeles and on their units; an additive measure $\nu_{\mathrm{add}}$ equal to $|a|^{1/2}$ times the pushforward of Lebesgue measure along the inverse of the mixed-space ring equivalence, and a Haar measure $\nu_{\mathrm{mul}}$ on the units.
--
--   **The real parameter $P$ and its Whittaker package.** A parameter $P$ of type `RealArchParam`, with `_hP₁`: in the principal case $P=\mathrm{principal}(u_1,a_1,u_2,a_2)$ one has $|\mathrm{Re}(u_1-u_2)|<1$. Weights $kw$, radial functions $Wr$ and a function $WA$ on $\mathrm{GL}_2(\mathbb{R})$, all indexed by a parity $\mathrm{par}\in\mathbb{Z}/2$ (and, for $kw$ and $Wr$, by an infinite place of $\mathbb{Q}$), subject to: `hkw1`, in the principal case $kw\,\mathrm{par}\,w=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$, where $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$; `hkw2`, in the discrete case $P=\mathrm{discrete}(u_0,n)$ with $n\ge 1$, $kw\,\mathrm{par}\,w=n+1$; `hWr1`, in the even principal case $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$ with $\mathrm{par}=a_1$, $Wr\,\mathrm{par}\,w(-t)=(-1)^{a_1.\mathrm{val}}Wr\,\mathrm{par}\,w(t)$; `hWr2`, in the discrete case $Wr\,\mathrm{par}\,w$ vanishes on the negative reals; `hWr3`, in the even principal case with $\mathrm{par}=a_1+1$ there is an abscissa beyond which $t\mapsto (Wr\,\mathrm{par}\,w(t)+(-1)^{a_1.\mathrm{val}}Wr\,\mathrm{par}\,w(-t))/t$ is Mellin convergent with Mellin transform $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}\,0\,a_1$ at $s$; `hWr4`, for every parity $\mathrm{par}$ and every $b'$ with $b'=\mathrm{par}$ or $b'=\mathrm{par}+P.\mathrm{centralSign}$ there is an abscissa beyond which the analogous symmetrised quotient with sign $(-1)^{b'.\mathrm{val}}$ is Mellin convergent with Mellin transform the archimedean factor of $P.\mathrm{twist}\,0\,b'$ at $s$. Further, $WA$ is a Whittaker function for $P$: `hWAN` gives $WA\,\mathrm{par}(\mathrm{unipotentGL2}(x)h)=e^{-2\pi i a x}WA\,\mathrm{par}(h)$; `hWAZ` gives the central law $WA\,\mathrm{par}(z\cdot h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}\,WA\,\mathrm{par}(h)$ for scalar matrices; `hWAK` gives right equivariance $WA\,\mathrm{par}(h\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(kw\,\mathrm{par}\,\mathrm{default})(\kappa)\,WA\,\mathrm{par}(h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt` gives $WA\,\mathrm{par}(\mathrm{diag}(t,1))=Wr\,\mathrm{par}\,\mathrm{default}(t)$ for $t\in\mathbb{R}^\times$; and `hWAc` gives continuity of each $WA\,\mathrm{par}$. Finally $w_0^{R}\in\mathrm{GL}_2(\mathbb{R})$ is the element with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   **The parameter $P_2$ and the datum $D$.** A real place $w_0$ of $K$ and a parameter $P_2$ with `hP₂`: either $K$ has exactly three real places $w_0,w_1,w_2$, pairwise distinct and exhausting the infinite places, and $P_2=\mathrm{principal}(uR\,w_1,aR\,w_1,uR\,w_2,aR\,w_2)$; or $K$ has one complex place $w_C$ and the infinite places are $w_C$ and $w_0$, and $P_2=\mathrm{discrete}(uC\,w_C,|kC\,w_C|)$ when $kC\,w_C\neq0$, while $P_2=\mathrm{principal}(uC\,w_C,0,uC\,w_C,1)$ when $kC\,w_C=0$. An archimedean datum $D$ of type `ArchDatumR P₂` (a Whittaker function $D.W$ on $2\times2$ real matrices together with smoothness, unipotent and central laws, an entire zeta function with its integral representation, functional equation, finite order and decay estimates), an integer $k_0$, and: `hDW`, $D.W(x\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, $D$ is a Casimir eigenfunction, $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for invertible $x$; `hDnz`, $D.W$ is not identically zero; `hk₀min`, in the principal case $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$, and in the discrete case $k_0=m+1$.
--
--   **Profile hypotheses.** Complex numbers $\nu_1,\nu_2$ and $b\in\mathbb{Z}/2$ with `hPev`: $P=\mathrm{principal}(\nu_1,b,\nu_2,b)$ (an even principal parameter); `hk₀`: $k_0=0$; `hLevi`: in the principal case for $P_2$ the first sign is $b+1$; $\delta\in\{0,1\}$ with $\delta\equiv aR\,w_0+b \pmod 2$; and the seed $S$ on $2\times3$ real matrices given explicitly by
--   $$S(M)=(M_{00}M_{11}-M_{01}M_{10})^{\delta}\bigl((M_{00}+iM_{10})^2+(M_{01}+iM_{11})^2\bigr)(M_{02}-iM_{12})^2\,e^{-\pi\sum_{i,j}M_{ij}^2}.$$
--   Lastly $u_1,u_2\in\mathbb{C}$ and $c\in\mathbb{Z}/2$ with `hP₂eq`: $P_2=\mathrm{principal}(u_1,c,u_2,c)$, and $\rho\in\mathbb{C}$ with `hρ`: for all $\tau>0$,
--   $$D.W\bigl(\mathrm{diag}(\tau,1)\bigr)=\rho\,\tau\cdot 4\int_{0}^{\infty} r^{u_1}e^{-\pi r^2}\,(\tau/r)^{u_2}e^{-\pi(\tau/r)^2}\,\frac{dr}{r}.$$
--
--   **Conclusion.** There exists $\sigma_a\in\mathbb{R}$ such that for every $s$ with $\mathrm{Re}\,s>\sigma_a$ the double integral over $a_2\in(0,\infty)$ and $a_1\in\mathbb{R}$ of the integrand which, for $a_1\neq0$ and $a_2>0$, is formed from $q:=\mathrm{upperUnit}(a_1,0,a_2)\in\mathrm{GL}_2(\mathbb{R})$, the matrix $\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$, as
--   $$\Bigl(|\det q|\;WA\,b\bigl(w_0^{R}\,{}^{t}q^{-1}\bigr)\cdot \bigl(\mathrm{dualWhittakerFn3}\,\Phi\bigr)\bigl(\iota(q)_{\infty}\bigr)\Bigr)\,|\det q|^{\,s-1/2}\cdot a_1^{-2},$$
--   and is $0$ otherwise, equals
--   $$\Bigl(\bigl(\varepsilon_\infty\,(-1)^{(P.\mathrm{centralSign}).\mathrm{val}}\,(-1)^{r_2}\bigr)\cdot\bigl(2\pi\,(-1)^{b.\mathrm{val}}\,\rho\bigr)\Bigr)\cdot\Gamma^{\vee}_{\mathbb{R}}(s)\,\Gamma^{\vee}_{\mathbb{C}}(s).$$
--   Here: $\Phi=\mathrm{jacquetVector3}(D,uR\,w_0,aR\,w_0,a,psiInf,S)$, so that $\Phi(g)=\mathrm{quasiChar}(uR\,w_0+1,aR\,w_0)(\det \mathrm{realMat}\,g)\int_{e}\mathrm{jacquetIntegrand3}(\dots)$, and $\mathrm{dualWhittakerFn3}\,\Phi(g)=\Phi(\mathrm{longWeyl3}\cdot {}^{t}g^{-1})$; the argument $\iota(q)_\infty$ is the archimedean component of the image of $q$ under the embedding of $\mathrm{GL}_2(\mathbb{R})$ at the real place of $\mathbb{Q}$ into the adelic $\mathrm{GL}_2$ followed by `iota` into the adelic $\mathrm{GL}_3$; $\varepsilon_\infty$ is `archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC`, the product over the real places of the epsilon factors of $P$ twisted by $(uR\,w,aR\,w)$ times the product over the complex places of the epsilon factors of the base change of $P$ twisted by $(uC\,w,kC\,w)$; $r_2$ is the number of complex places of $K$; and $\Gamma^{\vee}_{\mathbb{R}}(s)$, $\Gamma^{\vee}_{\mathbb{C}}(s)$ are the products of $\Gamma_{\mathbb{R}}(s+1/2+x)$ over the multiset `twistedGammaR` and of $\Gamma_{\mathbb{C}}(s+1/2+x)$ over the multiset `twistedGammaC`, both formed from the dual parameters $(\mathrm{archOfParamR}\,K\,P)^{\vee}$, $(\mathrm{archOfParamC}\,K\,P)^{\vee}$ twisted by the negated exponents $-uR$, $aR$, $-uC$, $-kC$. Thus the dual torus pair is the product of the symbolic archimedean root number, the explicit constant $2\pi(-1)^{b.\mathrm{val}}\rho$, and the dual gamma factor.
--
--   This is the dual half of the archimedean Rankin–Selberg torus-pair computation for the $\mathrm{GL}_3\times\mathrm{GL}_2$ integral attached to a non-base-change cubic idele class character, in the even principal profile with the quadratic seed $S$, with the proportionality constant evaluated as $2\pi(-1)^{b}\rho$. It feeds the combined unfolded-and-dual statement [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3), which supplies the archimedean functional-equation input to the converse theorem used in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_profile.lean

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

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell
open LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_profile
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
    (hk₀ : k₀ = 0)
    (hLevi : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P₂ = RealArchParam.principal u₁ a₁ u₂ a₂ → a₁ = b + 1)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = aR w₀ h₀ + b)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) ^ 2 + (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ)) ^ 2) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ 2) * gaussian3 M)

    (u₁ u₂ : ℂ) (c : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c u₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((τ) / r : ℝ) : ℂ) ^ (u₂) * (Real.exp (-(Real.pi * ((τ) / r) ^ 2)) : ℂ)) / (r : ℂ))) :
    ∃ σa : ℝ, ∀ s : ℂ, σa < s.re →
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA b (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = ((archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val * (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card) * ((((2 * Real.pi : ℝ) : ℂ) * (-1 : ℂ) ^ b.val) * ρ)) * (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
                    (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod) := by sorry
