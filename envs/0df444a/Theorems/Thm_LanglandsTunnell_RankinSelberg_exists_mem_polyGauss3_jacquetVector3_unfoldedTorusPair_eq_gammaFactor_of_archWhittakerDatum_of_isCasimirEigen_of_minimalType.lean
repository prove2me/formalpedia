-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_mem_polyGauss3_jacquetVector3_unfoldedTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_minimalType
-- name    : LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_jacquetVector3_unfoldedTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_minimalType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/79b5025c-7206-5b93-9b23-c52440e431af
-- title:
--   Unfolded archimedean GL₂× GL₃ torus-pair identity at minimal type
-- statement:
--   Throughout, $K$ is a number field of degree $3$ over $\mathbb{Q}$ whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra (hypothesis `_hdeg` together with the algebra assumptions), and $\mu\colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ is a character.
--
--   **Hypotheses on $\mu$.** `_hμ` asserts `IsAdmissibleTwist K μ`: $\mu$ is trivial on the principal ideles, continuous, and unitary. `_hns` asserts that there is *no* admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose trace $\mathfrak{p}=\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ is a place of unramifiedness of $\eta$, the value $\mu(\varpi_{\mathfrak{P}})$ equals $\eta(\varpi_{\mathfrak{p}})$ raised to the inertia degree of $\mathfrak{P}$ over $\mathfrak{p}$, where $\varpi_\bullet$ denotes the idele `uniformizerIdele` at the place in question.
--
--   **Archimedean data for $\mu$.** Functions $uR, aR$ on the real places and $uC, kC$ on the complex places of $K$ (with values in $\mathbb{C}$, $\mathbb{Z}/2$, $\mathbb{C}$, $\mathbb{Z}$ respectively) are given, and `huR`, `huC` say that $\mu$ has `IsArchCompAt` local behaviour at each infinite place: at a real place $w$ its local component is $x\mapsto \|x\|^{\mathrm{mult}(w)\,uR(w)}\,(x/\|x\|)^{aR(w).\mathrm{val}}$, and at a complex place $w$ the same formula with exponents $uC(w)$ and $kC(w)$.
--
--   **The character $\omega$ on $\mathbb{Q}$.** `hω` has three clauses: $\omega$ is an admissible twist of $\mathbb{Q}$; for every prime $p$ of $\mathcal{O}_\mathbb{Q}$ that is not a bad place for $(K,\mu)$ (i.e. $p$ is neither ramified in $K$ nor twist-ramified above), $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals $\mathrm{inducedE3}$ of the coefficient system $\mathfrak{P}\mapsto \mu(\varpi_{\mathfrak{P}})$ at $p$, namely minus the degree-$3$ coefficient of the induced Euler polynomial; and, for every choice of archimedean exponents $(uR,aR,uC,kC)$ satisfying the two `IsArchCompAt` conditions for $\mu$, the character $\omega$ has `IsArchCompAt` behaviour at the real place of $\mathbb{Q}$ with exponent $\sum_w uR(w)+\sum_w 2\,uC(w)$ and sign exponent $\sum_w aR(w).\mathrm{val}+\sum_w (kC(w)+1)$ (finite sums over the real, resp. complex, places of $K$).
--
--   **Splitting of the ideles and the additive character.** $E\colon (\mathbb{A}_{\mathbb{Q},\infty})^\times\to(\mathbb{A}_\mathbb{Q})^\times$ satisfies `hE`: the infinite part of $E(u)$ is $u$ and its finite part is $1$. A rational number $a$ is given with $a\neq 0$ and $a=-1$, together with a unit $a_\infty$ of the infinite adeles equal to the image of $a$, and $\psi_\infty$ is the additive character $x\mapsto \psi_{\mathrm{arch}}(a x)$ for the standard archimedean character (`hpsiInf`). Measure data: $\nu_{\mathrm{add}}$ on $\mathbb{A}_{\mathbb{Q},\infty}$ is the Lebesgue measure of the mixed space transported by `InfiniteAdeleRing.ringEquiv_mixedSpace`$^{-1}$ and scaled by $|a|^{1/2}$ (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on $(\mathbb{A}_{\mathbb{Q},\infty})^\times$; the relevant measurable and Borel structures are assumed.
--
--   **The parameter $P$ and the real Whittaker data.** $P$ is a `RealArchParam`, i.e. either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u,k)$ with $k\ge 1$; `_hP₁` requires $|\mathrm{Re}(u_1-u_2)|<1$ in the principal case. Weights $kw\colon \mathbb{Z}/2\times \mathrm{InfinitePlace}(\mathbb{Q})\to\mathbb{Z}$, radial functions $Wr\colon \mathbb{Z}/2\times\mathrm{InfinitePlace}(\mathbb{Q})\times\mathbb{R}\to\mathbb{C}$ and functions $WA\colon \mathbb{Z}/2\times GL_2(\mathbb{R})\to\mathbb{C}$ are given, subject to: `hkw1`, `hkw2` fixing the weight ($kw(\mathrm{par})=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ in the principal case, $n+1$ in the discrete case); `hWr1` (in the principal case with equal parities $a_1=a_2$ and $\mathrm{par}=a_1$, $Wr$ has parity $(-1)^{a_1.\mathrm{val}}$), `hWr2` (in the discrete case $Wr$ vanishes on $t<0$), `hWr3` (in the principal case with equal parities and $\mathrm{par}=a_1+1$, for $\mathrm{Re}\,s$ large the Mellin transform of $t\mapsto (Wr(t)+(-1)^{a_1.\mathrm{val}}Wr(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}(0,a_1)$), and `hWr4` (for every $\mathrm{par}$ and every $b\in\{\mathrm{par},\,\mathrm{par}+P.\mathrm{centralSign}\}$, the same Mellin transform with sign $(-1)^{b.\mathrm{val}}$ converges and equals the archimedean factor of $P.\mathrm{twist}(0,b)$ for $\mathrm{Re}\,s$ large). The functions $WA(\mathrm{par},\cdot)$ are Whittaker functions on $GL_2(\mathbb{R})$: `hWAN` gives the unipotent law with character $x\mapsto e^{-2\pi i a x}$, `hWAZ` the central law with $|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}$, `hWAK` right equivariance under `rowIsometrySubgroup₀ ℝ` by the weight character `archWeightCharℝ (kw par default)`, `hWAt` the restriction to the torus $\mathrm{diag}(t,1)$ being $Wr(\mathrm{par},\mathrm{default},t)$, and `hWAc` continuity. Finally $w_{0R}\in GL_2(\mathbb{R})$ is the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   **The complementary place and parameter.** $w_0$ is a real place of $K$, and $P_2$ is a `RealArchParam` satisfying `hP₂`: either $K$ has exactly three real places $w_0,w_1,w_2$ (pairwise distinct, exhausting the infinite places) and $P_2=\mathrm{principal}(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$, or $K$ has one complex place $w_C$ and the real place $w_0$ only, and $P_2=\mathrm{discrete}(uC(w_C),|kC(w_C)|)$ when $kC(w_C)\neq 0$, while $P_2=\mathrm{principal}(uC(w_C),0,uC(w_C),1)$ when $kC(w_C)=0$.
--
--   **The $GL_2$ datum.** $D$ is an `ArchDatumR P₂` (a Whittaker function $D.W$ on $M_2(\mathbb{R})$ with the smoothness, unipotent and central laws, entire completed zeta integrals, functional equation, finite order and decay axioms of that structure) and $k_0\in\mathbb{Z}$, subject to: `hDW`, right equivariance of $D.W$ under `rowIsometrySubgroup₀ ℝ` by `archWeightCharℝ k₀`; `hDE`, the Casimir eigenvalue equation $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all $x$ with $\det x\neq 0$; `hDnz`, nonvanishing of $D.W$ at some $g\in GL_2(\mathbb{R})$; and `hk₀min`, minimality of the type: $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2 \bmod 2$ if $P_2=\mathrm{principal}(u_1,a_1,u_2,a_2)$, and $k_0=m+1$ if $P_2=\mathrm{discrete}(u,m)$.
--
--   **Conclusion.** There exists $S$ in `polyGauss3` — a function on $M_{2\times 3}(\mathbb{R})$ of the form (polynomial in the entries) $\times$ `gaussian3` — such that, writing $J(S)=\mathrm{jacquetVector3}\,D\,(uR(w_0))\,(aR(w_0))\,a\,\psi_\infty\,S$ for the associated vector on $GL_3$ of the infinite adeles, the following hold.
--
--   (i) $J(S)\neq 0$.
--
--   (ii) There is an admissible twist $\sigma$ of $\mathbb{Q}$ and some $s\in\mathbb{C}$ with $\mathrm{archZeta30}\,\nu_{\mathrm{mul}}\,J(S)\,(\sigma\circ E)\,s\,1\neq 0$, the integral over $(\mathbb{A}_{\mathbb{Q},\infty})^\times$ of $J(S)(\iota_{GL}(\mathrm{diag}(\alpha,1,1))\,)\,\sigma(E\alpha)\,\|\alpha\|^{s-1}$ being nonzero.
--
--   (iii) There are a parity $\mathrm{par}_0\in\mathbb{Z}/2$, an abscissa $\sigma_a\in\mathbb{R}$ and constants $e,ed\in\mathbb{C}$ with $e\neq 0$, $ed\neq 0$ and
--   $$ed=\Bigl(\mathrm{archRootNumber}\,K\,(\mathrm{archOfParamR}\,K\,P)\,(\mathrm{archOfParamC}\,K\,P)\,uR\,aR\,uC\,kC\cdot(-1)^{P.\mathrm{centralSign}.\mathrm{val}}\cdot(-1)^{\#\{\text{complex places of }K\}}\Bigr)\,e,$$
--   where the root number is the product over the real places of the epsilon factors of $P$ twisted by $(uR,aR)$ times the product over the complex places of the epsilon factors of the base change $P.\mathrm{baseChange}$ twisted by $(uC,kC)$, such that the four following assertions hold.
--
--   (a) For every $k$ in [`AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℝ`](def/AutomorphicForm_RowIsometryInvariance.html#L110) with $\det k=1$ and every $q\in GL_2(\mathbb{R})$,
--   $$WA(\mathrm{par}_0,qk)\cdot J(S)\bigl(\iota(q k)\bigr)=WA(\mathrm{par}_0,q)\cdot J(S)\bigl(\iota(q)\bigr),$$
--   where $\iota(\cdot)$ abbreviates the archimedean component at the unique infinite place of $\mathbb{Q}$ of the image in adelic $GL_3$ of `archRealGLAt` applied to the argument.
--
--   (b) The same invariance for the dual vector: for such $k$ and all $q$,
--   $$|\det(qk)|\,WA(\mathrm{par}_0,w_{0R}\cdot{}^{t}(qk)^{-1})\cdot \mathrm{dualWhittakerFn3}\,J(S)\bigl(\iota(qk)\bigr)=|\det q|\,WA(\mathrm{par}_0,w_{0R}\cdot{}^{t}q^{-1})\cdot\mathrm{dualWhittakerFn3}\,J(S)\bigl(\iota(q)\bigr),$$
--   where $\mathrm{dualWhittakerFn3}\,W(g)=W(\mathrm{longWeyl3}\cdot{}^{t}g^{-1})$.
--
--   (c) The unfolded torus-pair identity: for every $s$ with $\sigma_a<\mathrm{Re}\,s$,
--   $$\int_{M_2(\mathbb{R})}\chi_{uR(w_0)+2,\,aR(w_0)}(\det x)\,|\det x|^{-2}\Bigl(\int_{\mathbb{R}}Wr(\mathrm{par}_0,\mathrm{default},t)\,D.W\bigl(\mathrm{diag}(at,1)\,x^{-1}\bigr)|t|^{s-\frac12}\,t^{-2}\,dt\Bigr)\Bigl(\int_0^\infty y^{P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\,\mathrm{godementInner3}\bigl(\psi_\infty\cdot(y),S,x,1\bigr)\,dy\Bigr)\,dx$$
--   $$=e\cdot\prod_{x\in \mathrm{twistedGammaR}\,K\,(\mathrm{archOfParamR}\,K\,P)\,uR\,aR}\Gamma_{\mathbb{R}}(s+\tfrac12+x)\cdot\prod_{x\in\mathrm{twistedGammaC}\,K\,(\mathrm{archOfParamR}\,K\,P)\,(\mathrm{archOfParamC}\,K\,P)\,uR\,aR\,uC\,kC}\Gamma_{\mathbb{C}}(s+\tfrac12+x),$$
--   the two multisets being the sums of the $\Gamma_{\mathbb{R}}$- resp. $\Gamma_{\mathbb{C}}$-shift multisets of the twisted local parameters over the infinite places of $K$; here $\chi_{u,a}$ is `ArchR.quasiChar`, $\mathrm{diag}(y,1)$ is `ArchR.diagOne`, $\psi_\infty\cdot(y)$ is the `mulShift` of $\psi_\infty$ by the image of $y$ in the infinite adeles, and $\mathrm{godementInner3}$ is the partial Fourier integral $\int_{\mathbb{R}^2}S\bigl(x\cdot[\,m_0+v_0m_2\mid m_1+v_1m_2\,]\bigr)\psi(-v_1)\,dv$ evaluated at $m=1$. (In the Lean the outer integration variable carries the same letter as the constant $e$.)
--
--   (d) The dual torus identity: for every $s$ with $\sigma_a<\mathrm{Re}\,s$,
--   $$\int_{0}^{\infty}\int_{\mathbb{R}}\Bigl[|\det q|\,WA(\mathrm{par}_0,w_{0R}\cdot{}^{t}q^{-1})\cdot\mathrm{dualWhittakerFn3}\,J(S)\bigl(\iota(q)\bigr)\Bigr]\,|\det q|^{s-\frac12}\,a_1^{-2}\,da_1\,da_2=ed\cdot\Gamma\text{-product},$$
--   where $q=\mathrm{upperUnit}(a_1,0,a_2)=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$ for $a_1\neq 0$, $a_2>0$ (the integrand being $0$ otherwise), and the $\Gamma$-product is the corresponding product of $\Gamma_{\mathbb{R}}(s+\frac12+x)$ over $\mathrm{twistedGammaR}\,K$ formed from the duals $(\mathrm{archOfParamR}\,K\,P)^\vee$ with exponents $-uR$ and parities $aR$, times the product of $\Gamma_{\mathbb{C}}(s+\frac12+x)$ over $\mathrm{twistedGammaC}\,K$ formed from the duals of $\mathrm{archOfParamR}\,K\,P$ and $\mathrm{archOfParamC}\,K\,P$ with exponents $-uR,aR,-uC,-kC$.
--
--   The statement differs from its companion with a folded first identity only in clause (c), where the $GL_2\times GL_3$ torus-pair integral is replaced by the explicit iterated integral over $M_2(\mathbb{R})$ displayed above.
--
--   This is the archimedean $GL_2\times GL_3$ Rankin–Selberg input for the converse-theorem step of the cubic induction: it produces a polynomial-times-Gaussian Schwartz datum whose Jacquet–Whittaker vector pairs, against a Casimir-eigen $GL_2(\mathbb{R})$ Whittaker datum of minimal $SO_2$-type, with exactly the expected completed $\Gamma$-factors at $s$ and at the dual point, with ratio the archimedean root number. It is cited by the version in which the first identity appears in folded torus-pair form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_mem_polyGauss3_jacquetVector3_unfoldedTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_minimalType.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_jacquetVector3_unfoldedTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_minimalType
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
      (∀ (u : ℂ) (m : ℕ) (hm : 1 ≤ m), P₂ = RealArchParam.discrete u m hm → k₀ = (m : ℤ) + 1)) :
    ∃ S ∈ polyGauss3, (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) ≠ 0 ∧
      (∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (σ.comp E) s 1 ≠ 0) ∧
      ∃ (par₀ : ZMod 2) (σa : ℝ) (e ed : ℂ), e ≠ 0 ∧ ed ≠ 0 ∧
        ed = (archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val * (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card) * e ∧
        (∀ k ∈ AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 → ∀ q : GL (Fin 2) ℝ,
            WA par₀ (q * k) * (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (q * k))))
              = WA par₀ q * (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) ∧
        (∀ k ∈ AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 → ∀ q : GL (Fin 2) ℝ,
            ((((|(Matrix.GeneralLinearGroup.det (q * k) : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv (q * k))) *
                dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (q * k)))))
              = ((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) *
                dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q))))) ∧
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
              = ed * (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
                    (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod)) := by sorry
