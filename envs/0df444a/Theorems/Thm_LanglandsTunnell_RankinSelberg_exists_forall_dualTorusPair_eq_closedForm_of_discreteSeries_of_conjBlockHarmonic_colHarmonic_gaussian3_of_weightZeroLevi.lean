-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_dualTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_weightZeroLevi
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_weightZeroLevi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/8eef1405-8741-560f-a9a6-35b8bf27cfd3
-- title:
--   Closed form of the dual torus pair: weight-zero Levi branch
-- statement:
--   Throughout, $K$ is a number field of degree $3$ over $\mathbb{Q}$ (hypothesis `_hdeg`), with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, and $\mu \colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ is a character subject to `_hμ`, which asserts that $\mu$ is an admissible twist: trivial on the image of $K^\times$, continuous, and of absolute value $1$ at every idele. The hypothesis `_hns` excludes descent: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified (its local component trivial on the units of the completion's valuation ring) and with $\eta$ unramified at $\mathfrak{P} \cap \mathcal{O}_{\mathbb{Q}}$, the value $\mu$ of a uniformizer idele at $\mathfrak{P}$ equals the value of $\eta$ at a uniformizer idele of $\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ raised to the inertia degree.
--
--   Archimedean data for $\mu$: functions $uR, aR$ on the real places and $uC, kC$ on the complex places of $K$, valued in $\mathbb{C}$, $\mathbb{Z}/2$, $\mathbb{C}$, $\mathbb{Z}$ respectively, with `huR` and `huC` requiring, for every real place $w$ (respectively complex place), that the archimedean local component of $\mu$ at $w$ be $x \mapsto \lVert x\rVert^{\,\mathrm{mult}(w)\,u} (x/\lVert x\rVert)^{a}$ with $(u,a) = (uR\,w, (aR\,w).\mathrm{val})$ (respectively $(uC\,w, kC\,w)$). A character $\omega$ of $(\mathbb{A}_{\mathbb{Q}})^\times$ is given, and `hω` has three clauses: $\omega$ is an admissible twist of $\mathbb{Q}$; at every finite place $p$ of $\mathbb{Q}$ which is not bad for $(K,\mu)$ — bad meaning either ramified in $K$ (some prime above $p$ has ramification index $\ne 1$) or carrying a prime above $p$ at which $\mu$ is ramified — the character $\omega$ is unramified at $p$ and its Euler coefficient (the value at a uniformizer idele) equals $\mathrm{inducedE3}$ of the unramified coefficient family of $\mu$ at $p$, that is minus the coefficient of degree $3$ of the induced Euler polynomial; and, for any archimedean data $uR, aR, uC, kC$ satisfying the two relations above, at every real place $v$ of $\mathbb{Q}$ the archimedean component of $\omega$ at $v$ has exponent $\sum_{w \text{ real}} uR\,w + \sum_{w \text{ complex}} 2\,uC\,w$ and integer parameter $\sum_{w\text{ real}} (aR\,w).\mathrm{val} + \sum_{w\text{ complex}} (kC\,w + 1)$ (finite sums over the infinite places).
--
--   Adelic normalisations: a homomorphism $E$ from the units of the infinite adeles of $\mathbb{Q}$ to the ideles, with `hE` stating that $E(u)$ has infinite part $u$ and trivial finite part; a rational $a$ with $a \ne 0$ and $a = -1$; a unit $a_{\infty}$ of the infinite adeles whose underlying element is the image of $a$; an additive character $\psi_{\infty}$ with $\psi_\infty(x) = \psi_{\mathrm{arch}}(a x)$ for the standard archimedean character; measurable-space and Borel structures on the infinite adeles and on their unit group; an additive measure $\nu_{\mathrm{add}}$ equal to $|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the identification of the infinite adeles with the mixed space; and a Haar measure $\nu_{\mathrm{mul}}$ on the units of the infinite adeles.
--
--   The archimedean $\mathrm{GL}_2$ profile over $\mathbb{Q}$: a real archimedean parameter $P$, which is either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u,k)$ with $k \ge 1$, subject to `_hP₁` (in the principal case $|\mathrm{Re}(u_1-u_2)| < 1$); weights $kw \colon \mathbb{Z}/2 \to \{\text{places of }\mathbb{Q}\} \to \mathbb{Z}$, radial profiles $Wr$, and functions $WA$ on $\mathrm{GL}_2(\mathbb{R})$, all indexed by a parity. The weight laws `hkw1`, `hkw2` give $kw\,\mathrm{par}\,w = \mathrm{signShift}(a_1+\mathrm{par}) + \mathrm{signShift}(a_2+\mathrm{par})$ in the principal case (where $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$) and $kw\,\mathrm{par}\,w = k+1$ in the discrete case, at real places $w$ of $\mathbb{Q}$. The radial laws are: `hWr1`, for $P = \mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par} = a_1$, the parity relation $Wr\,\mathrm{par}\,w(-t) = (-1)^{a_1.\mathrm{val}} Wr\,\mathrm{par}\,w(t)$; `hWr2`, in the discrete case $Wr\,\mathrm{par}\,w(t) = 0$ for $t<0$; `hWr3`, for $P = \mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par} = a_1+1$, the Mellin transform of $t \mapsto (Wr\,\mathrm{par}\,w(t) + (-1)^{a_1.\mathrm{val}} Wr\,\mathrm{par}\,w(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P$ twisted by $(0,a_1)$, for $\mathrm{Re}\,s$ large (the archimedean factor of a principal parameter at $s$ being $\Gamma_{\mathbb{R}}(s+u_1+\mathrm{signShift}\,a_1)\Gamma_{\mathbb{R}}(s+u_2+\mathrm{signShift}\,a_2)$, and of a discrete parameter $\Gamma_{\mathbb{C}}(s+u+k/2)$, while twisting by $(u,a)$ shifts all exponents by $u$ and all signs by $a$); and `hWr4`, for every $b$ with $b = \mathrm{par}$ or $b = \mathrm{par} + P.\mathrm{centralSign}$, the same Mellin transform with $(-1)^{b.\mathrm{val}}$ converges and equals the archimedean factor of $P$ twisted by $(0,b)$ for $\mathrm{Re}\,s$ large. The laws for $WA$ are: `hWAN`, equivariance $WA\,\mathrm{par}(n(x)h) = e^{-2\pi i a x} WA\,\mathrm{par}(h)$ under upper unipotents; `hWAZ`, $WA\,\mathrm{par}(z\cdot h) = |z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}} WA\,\mathrm{par}(h)$ for scalar matrices; `hWAK`, right translation by $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ` multiplies $WA\,\mathrm{par}$ by the weight character `archWeightCharℝ` of weight $kw\,\mathrm{par}$ at the default place; `hWAt`, $WA\,\mathrm{par}(\mathrm{diagOne}\,t) = Wr\,\mathrm{par}(t)$ at the default place; and `hWAc`, continuity of each $WA\,\mathrm{par}$. Finally $w_{0R} \in \mathrm{GL}_2(\mathbb{R})$ is the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   The $\mathrm{GL}_2$ datum attached to the remaining infinite places of $K$: a real place $w_0$ of $K$, a real archimedean parameter $P_2$, and `hP₂`, which asserts that either $K$ has exactly the three distinct real places $w_0,w_1,w_2$ and $P_2 = \mathrm{principal}(uR\,w_1, aR\,w_1, uR\,w_2, aR\,w_2)$, or $K$ has exactly the places $w_0$ and one complex place $w_C$, and then either $kC\,w_C \ne 0$ and $P_2 = \mathrm{discrete}(uC\,w_C, |kC\,w_C|)$, or $kC\,w_C = 0$ and $P_2 = \mathrm{principal}(uC\,w_C, 0, uC\,w_C, 1)$. Further, $D$ is an `ArchDatumR P₂`, that is a Whittaker function $D.W$ on real $2\times 2$ matrices, smooth on the invertible locus, with the unipotent and central transformation laws for $P_2$, together with its entire zeta functions, their integral representations via the archimedean factor of twists of $P_2$, the functional equation with the epsilon factor of $P_2$, finite order in vertical strips and the decay estimates at $0$ and $\infty$; $k_0 \in \mathbb{Z}$; `hDW` says $D.W(x\kappa) = \mathrm{archWeightChar}_{\mathbb{R}}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE` says $D$ is a Casimir eigenfunction, $-\bigl(\tfrac14 H^2 - \tfrac12 H + E F\bigr) D.W = P_2.\mathrm{laplaceEigenvalue}\cdot D.W$ on invertible matrices, where the eigenvalue is $1/4 - ((u_1-u_2)/2)^2$ in the principal case and $(1-k^2)/4$ in the discrete case; `hDnz` says $D.W$ is nonzero at some element of $\mathrm{GL}_2(\mathbb{R})$; and `hk₀min` requires $k_0 \in \{0,1\}$ with $k_0 \equiv a_1+a_2 \pmod 2$ when $P_2$ is principal, and $k_0 = m+1$ when $P_2 = \mathrm{discrete}(u,m)$.
--
--   The branch considered is the following specialisation. $P = \mathrm{discrete}(u_P, n_P)$ with $n_P \ge 1$ (hypothesis `hPdisc`), $m = n_P+1$, and $n \in \mathbb{N}$, $\varepsilon' \in \mathbb{R}$ satisfy `hcol`: either $\varepsilon' = -1$ and $n = k_0 - m$, or $\varepsilon' = 1$ and $n = m - k_0$. A parity $\mathrm{par}_0$ is fixed, and the Schwartz datum $S$ on $2 \times 3$ real matrices is
--   $$S(M) = \bigl((M_{00} - i M_{10}) - i (M_{01} - i M_{11})\bigr)^m \,\bigl(M_{02} + \varepsilon' i M_{12}\bigr)^n\, e^{-\pi \sum_{i,b} M_{ib}^2}.$$
--   The profile at parity $\mathrm{par}_0$ and the default place of $\mathbb{Q}$ is one-sided and explicit: $Wr\,\mathrm{par}_0(t) = 2\,t^{\,u_P + n_P/2 + 1} e^{-2\pi t}$ for $t>0$ (`hWpos`) and $Wr\,\mathrm{par}_0(t) = 0$ for $t<0$ (`hWneg`). Moreover $k_0 = 0$, $P_2 = \mathrm{principal}(\mu_1, c, \mu_2, c)$ for some $\mu_1,\mu_2 \in \mathbb{C}$ and $c \in \mathbb{Z}/2$ (so $P_2.\mathrm{centralExponent} = \mu_1+\mu_2$), and a scalar $\rho \in \mathbb{C}$ is given with `hD`: for all $\tau > 0$,
--   $$D.W\bigl(\mathrm{diag}(\tau,1)\bigr) = \rho\,\tau\cdot\Bigl(4\int_0^{\infty} r^{\mu_1} e^{-\pi r^2}\,(\tau/r)^{\mu_2} e^{-\pi (\tau/r)^2}\,\frac{dr}{r}\Bigr).$$
--
--   Conclusion. There exists $\sigma_a \in \mathbb{R}$ such that for every $s \in \mathbb{C}$ with $\sigma_a < \mathrm{Re}\,s$ the iterated integral over $a_2 \in (0,\infty)$ and $a_1 \in \mathbb{R}$ of the integrand which vanishes unless $a_1 \ne 0$ and $a_2 > 0$, and which for such $(a_1,a_2)$, with $q := \begin{pmatrix} a_1 & 0 \\ 0 & a_2\end{pmatrix} \in \mathrm{GL}_2(\mathbb{R})$, equals
--   $$|\det q|\; WA\,\mathrm{par}_0\bigl(w_{0R}\,(q^{-1})^{\mathsf{T}}\bigr)\; \cdot\; \Bigl(\mathrm{dualWhittakerFn3}\,\bigl(\mathrm{jacquetVector3}\,D\,(uR\,w_0)\,(aR\,w_0)\,a\,\psi_\infty\,S\bigr)\Bigr)\bigl(\text{image of }q\bigr)\;\cdot\;|\det q|^{\,s-1/2}\cdot a_1^{-2},$$
--   is equal to
--   $$\pi\, i^m\,(-1)^{m+n+(aR\,w_0).\mathrm{val}}\,2^m\;\Gamma_{\mathbb{R}}\bigl(2s - P.\mathrm{centralExponent} - P_2.\mathrm{centralExponent} + n + 1\bigr)\;(2\pi)^{-(s - uR\,w_0 - u_P + m/2)}\;\Gamma\bigl(s - uR\,w_0 - u_P + m/2\bigr)\;\cdot\;\Bigl(2\rho\; B(Z+\mu_1, Z+\mu_2)\;\Gamma_{\mathbb{R}}(2Z+\mu_1+\mu_2)\Bigr),$$
--   where $Z := s - u_P - P_2.\mathrm{centralExponent} + m/2$, $B$ is the Euler beta integral, $\Gamma_{\mathbb{R}}(z) = \pi^{-z/2}\Gamma(z/2)$, and $P.\mathrm{centralExponent} = 2u_P$, $P_2.\mathrm{centralExponent} = \mu_1+\mu_2$ for the parameters at hand.
--
--   In the integrand, the argument of the dual Whittaker function is the archimedean component of the image of $q$ under the transport of $\mathrm{GL}_2(\mathbb{R})$ to $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ at the real place, followed by the block embedding $g \mapsto \mathrm{diag}(g,1)$ into $\mathrm{GL}_3$; $\mathrm{dualWhittakerFn3}\,W$ is $g \mapsto W(w_3 \cdot (g^{-1})^{\mathsf{T}})$ with $w_3$ the $3\times 3$ antidiagonal permutation matrix; and $\mathrm{jacquetVector3}\,D\,u_3\,a_3\,a\,\psi\,S$ at $g$ is the quasi-character value $\mathrm{quasiChar}(u_3+1)\,a_3$ of the determinant of the real matrix of $g$, times the integral over $e$ in the $2\times 2$ real matrices of `jacquetIntegrand3` for these data.
--
--   This is the archimedean computation of the dual half of the unfolded Rankin–Selberg torus integral for a $\mathrm{GL}_3 \times \mathrm{GL}_2$ pair arising from cubic induction, in the branch where the $\mathrm{GL}_2$ profile over $\mathbb{Q}$ is of discrete series type and the Levi datum is principal with weight $k_0 = 0$: the integral is evaluated in closed form as a product of gamma factors, a Laplace-type gamma factor, and a beta integral coming from the Gaussian convolution on the Levi. It feeds, together with its primal counterpart, into [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_threeReal_sameSign`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_threeReal_sameSign), which assembles the archimedean gamma factor required by the converse theorem in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_dualTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_weightZeroLevi.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_dualTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_weightZeroLevi
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
    (hk₀ : k₀ = 0) (μ₁ μ₂ : ℂ) (c : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal μ₁ c μ₂ c) (ρ : ℂ)
    (hD : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ))) :
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
              (ρ * (2 : ℂ) * Complex.betaIntegral ((s - uP - P₂.centralExponent + (m : ℂ) / 2) + μ₁) ((s - uP - P₂.centralExponent + (m : ℂ) / 2) + μ₂) *
                Complex.Gammaℝ (2 * (s - uP - P₂.centralExponent + (m : ℂ) / 2) + μ₁ + μ₂)) := by sorry
