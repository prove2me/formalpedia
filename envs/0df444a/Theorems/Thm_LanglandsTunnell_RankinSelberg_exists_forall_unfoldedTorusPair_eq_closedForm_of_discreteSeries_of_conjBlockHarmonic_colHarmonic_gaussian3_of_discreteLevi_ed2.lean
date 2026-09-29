-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_discreteLevi_ed2
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_discreteLevi_ed2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/e4bb20eb-0838-5035-91f2-a59d317c31a7
-- title:
--   Closed form of the unfolded torus pair: discrete Levi branch
-- statement:
--   Throughout, $K$ is a number field of degree $3$ over $\mathbb{Q}$ (hypothesis `_hdeg`), with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, and $\mu$ is a homomorphism $(\mathbb{A}_K)^\times \to \mathbb{C}^\times$.
--
--   **Global input on $\mu$ and $\omega$.** The hypothesis `_hμ` says that $\mu$ is an admissible twist: it is trivial on $K^\times$, continuous, and unitary (all its values have modulus $1$). The hypothesis `_hns` is the non-descent condition: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and whose restriction $p=\mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ is unramified for $\eta$, one has $\mu(\varpi_{\mathfrak{P}})=\eta(\varpi_{p})^{f(\mathfrak{P}/p)}$, where $\varpi$ denotes the uniformiser idele and $f$ the inertia degree. The families $u^{\mathbb{R}},a^{\mathbb{R}}$ (indexed by the real places of $K$, with values in $\mathbb{C}$ and $\mathbb{Z}/2$) and $u^{\mathbb{C}},k^{\mathbb{C}}$ (indexed by the complex places, with values in $\mathbb{C}$ and $\mathbb{Z}$) record the archimedean components of $\mu$: by `huR` and `huC`, at each place $w$ the local archimedean component of $\mu$ sends a unit $x$ of the completion to $\|x\|^{\mathrm{mult}(w)\,u_w}\,(x/\|x\|)^{a_w}$, with $a_w$ the integer lift of $a^{\mathbb{R}}_w$ in the real case and $k^{\mathbb{C}}_w$ in the complex case.
--
--   The character $\omega$ of $(\mathbb{A}_{\mathbb{Q}})^\times$ satisfies `hω`, a three-fold conjunction: (i) $\omega$ is an admissible twist of $\mathbb{Q}$; (ii) for every finite place $p$ of $\mathbb{Q}$ which is not bad for $(K,\mu)$ — i.e. $p$ is unramified in $K$ and $\mu$ is unramified at every prime of $K$ above $p$ — the character $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals $-$ the coefficient of $X^3$ in the Euler polynomial induced from the unramified Frobenius values $\mathfrak{P}\mapsto \mu(\varpi_{\mathfrak{P}})$ (set to $0$ at ramified $\mathfrak{P}$); (iii) for every choice of archimedean data $u^{\mathbb{R}},a^{\mathbb{R}},u^{\mathbb{C}},k^{\mathbb{C}}$ satisfying the same two conditions as in `huR`, `huC`, and every real place $v$ of $\mathbb{Q}$, the archimedean component of $\omega$ at $v$ has exponent $\sum_{w \text{ real}} u^{\mathbb{R}}_w+\sum_{w\text{ complex}}2u^{\mathbb{C}}_w$ and integer parameter $\sum_{w\text{ real}}(a^{\mathbb{R}}_w)^{\sharp}+\sum_{w\text{ complex}}(k^{\mathbb{C}}_w+1)$, the sums being finite sums over places.
--
--   **Adelic normalisations.** $E$ is a homomorphism $(\mathbb{A}_{\mathbb{Q},\infty})^\times\to(\mathbb{A}_{\mathbb{Q}})^\times$ splitting the infinite part: by `hE`, the infinite component of $E(u)$ is $u$ and its finite component is $1$. The rational number $a$ is nonzero and, by `ha1`, equal to $-1$; $a_\infty$ is a unit of the infinite adele ring whose underlying element is the image of $a$ (`haInf`). The additive character $\psi_\infty$ is, by `hpsiInf`, the standard archimedean character composed with multiplication by $a$, i.e. $\psi_\infty(x)=\psi_{\mathrm{arch}}(a x)$. The measure $\nu_{\mathrm{add}}$ on the infinite adele ring is $|a|^{1/2}$ times the transport of Lebesgue measure along the inverse of the identification with the mixed space (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on the units; measurability and Borel structures on these spaces are the ambient instances.
--
--   **The $GL_2$ archimedean profile over $\mathbb{Q}$.** $P$ is a real archimedean parameter (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u,k)$ with $k\ge 1$), subject to `_hP₁`: in the principal case $|\mathrm{Re}(u_1-u_2)|<1$. The data $k_w:\mathbb{Z}/2\times\{\text{places of }\mathbb{Q}\}\to\mathbb{Z}$, $W_r:\mathbb{Z}/2\times\{\text{places}\}\to(\mathbb{R}\to\mathbb{C})$ and $W_A:\mathbb{Z}/2\to (GL_2(\mathbb{R})\to\mathbb{C})$ satisfy: `hkw1`, in the principal case $k_w(\mathrm{par})=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$, where $\mathrm{signShift}(0)=0$ and $\mathrm{signShift}(1)=1$; `hkw2`, in the discrete case $P=\mathrm{discrete}(u_0,n)$ one has $k_w(\mathrm{par})=n+1$; `hWr1`, in the principal case with $a_1=a_2$ and $\mathrm{par}=a_1$, the parity law $W_r(-t)=(-1)^{a_1^{\sharp}}W_r(t)$; `hWr2`, in the discrete case $W_r(t)=0$ for $t<0$; `hWr3`, in the principal case with $a_1=a_2$ and $\mathrm{par}=a_1+1$, the existence of $\sigma_0$ such that for $\mathrm{Re}\,s>\sigma_0$ the Mellin transform of $t\mapsto (W_r(t)+(-1)^{a_1^{\sharp}}W_r(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}(0,a_1)$ at $s$; `hWr4`, for every $b$ equal to $\mathrm{par}$ or to $\mathrm{par}+\mathrm{centralSign}(P)$, the same Mellin transform (with $b$ in place of $a_1$) converges for $\mathrm{Re}\,s$ large and equals the archimedean factor of $P.\mathrm{twist}(0,b)$ at $s$. The function $W_A$ is a Whittaker model for this profile: `hWAN` gives $W_A(\mathrm{unip}(x)h)=e^{-2\pi i a x}W_A(h)$, `hWAZ` gives $W_A(zh)=|z|^{\,\mathrm{centralExponent}(P)+1}(z/|z|)^{\mathrm{centralSign}(P)^{\sharp}}W_A(h)$ for scalar $z\in\mathbb{R}^\times$, `hWAK` gives right equivariance $W_A(h\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(k_w(\mathrm{par}))(\kappa)\,W_A(h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`, `hWAt` identifies $W_A(\mathrm{diag}(t,1))$ with $W_r(\mathrm{par})$ at the default place, and `hWAc` asserts continuity of each $W_A(\mathrm{par})$. Finally $w_{0R}\in GL_2(\mathbb{R})$ is the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   **The Levi datum.** $w_0$ is a real place of $K$. The parameter $P_2$ satisfies `hP₂`, a disjunction describing the remaining archimedean places of $K$: either $K$ has three distinct real places $w_0,w_1,w_2$ exhausting all places and $P_2=\mathrm{principal}(u^{\mathbb{R}}_{w_1},a^{\mathbb{R}}_{w_1},u^{\mathbb{R}}_{w_2},a^{\mathbb{R}}_{w_2})$; or there is a complex place $w_C$ with $\{w_C,w_0\}$ exhausting all places and either $k^{\mathbb{C}}_{w_C}\neq 0$ and $P_2=\mathrm{discrete}(u^{\mathbb{C}}_{w_C},|k^{\mathbb{C}}_{w_C}|)$, or $k^{\mathbb{C}}_{w_C}=0$ and $P_2=\mathrm{principal}(u^{\mathbb{C}}_{w_C},0,u^{\mathbb{C}}_{w_C},1)$. Next, $D$ is an archimedean datum of type $P_2$, i.e. a function $\mathcal{W}_D$ on $2\times2$ real matrices, smooth on the invertible locus, with the unipotent law $\mathcal{W}_D(\mathrm{unip}(x)g)=\psi(x)\mathcal{W}_D(g)$, the central law $\mathcal{W}_D(zg)=\mathrm{centralChar}(P_2)(z)|z|\mathcal{W}_D(g)$, together with an entire completed zeta function whose torus integrals equal $\mathrm{archFactor}(P_2.\mathrm{twist}(u,a))(s)$ times it, the functional equation with epsilon factor $\varepsilon(P_2.\mathrm{twist}(u,a))$, polynomial-order bounds in vertical strips and the decay estimates at the torus. The integer $k_0$ and the hypotheses `hDW` (right equivariance $\mathcal{W}_D(xr)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(r)\mathcal{W}_D(x)$ for $r$ in `rowIsometrySubgroup₀ ℝ`), `hDE` ($\mathcal{W}_D$ is a Casimir eigenfunction on the invertible locus with eigenvalue $\mathrm{laplaceEigenvalue}(P_2)$), `hDnz` ($\mathcal{W}_D$ is not identically zero) and `hk₀min` (in the principal case $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2 \pmod 2$; in the discrete case $P_2=\mathrm{discrete}(u,m)$ one has $k_0=m+1$) pin down the weight.
--
--   **Discrete-series specialisation and the flat section.** By `hPdisc`, $P=\mathrm{discrete}(u_P,n_P)$ with $n_P\ge1$, and $m=n_P+1$ (`hm`). The pair $(n,\varepsilon')$ satisfies `hcol`: either $\varepsilon'=-1$ and $n=k_0-m$, or $\varepsilon'=1$ and $n=m-k_0$. A parity $\mathrm{par}_0\in\mathbb{Z}/2$ is fixed, and the section $S$ on $2\times3$ real matrices is given by `hS`:
--   $$S(M)=\bigl((M_{00}-iM_{10})-i(M_{01}-iM_{11})\bigr)^m\,\bigl(M_{02}+\varepsilon' i M_{12}\bigr)^n\,e^{-\pi\sum_{i,b}M_{ib}^2}.$$
--   The profile of $W_r(\mathrm{par}_0)$ at the default real place of $\mathbb{Q}$ is explicit: $W_r(t)=2t^{\,u_P+n_P/2+1}e^{-2\pi t}$ for $t>0$ (`hWpos`) and $W_r(t)=0$ for $t<0$ (`hWneg`). On the Levi side, $P_2=\mathrm{discrete}(\mu,k)$ with $k\ge1$ (`hP₂eq`), where $\mu$ here denotes a complex number (the name is reused, the idele class character of the same name being no longer accessible), and with a scalar $\rho\in\mathbb{C}$ one has $\mathcal{W}_D(\mathrm{diag}(\tau,1))=2\rho\,\tau^{\,\mu+k/2+1}e^{-2\pi\tau}$ for $\tau>0$ (`hDpos`) and $\mathcal{W}_D(\mathrm{diag}(-\tau,1))=0$ for $\tau>0$ (`hDneg`).
--
--   **Conclusion.** Under these hypotheses there exists $\sigma_a\in\mathbb{R}$ such that for every $s\in\mathbb{C}$ with $\sigma_a<\mathrm{Re}\,s$ the unfolded torus pair, namely the integral over $e\in\mathbb{R}^{2\times2}$
--   $$\int \chi_{u_{w_0}+2,\;a_{w_0}}(\det e)\;|\det e|^{-2}\;\Bigl(\int_{\mathbb{R}} W_r(t)\,\mathcal{W}_D\bigl(\mathrm{diag}(at,1)\,e^{-1}\bigr)\,|t|^{\,s-1/2}\,t^{-2}\,dt\Bigr)\Bigl(\int_0^\infty y^{\,c(P)+c(P_2)+2s}\,I_y(e)\,dy\Bigr)de,$$
--   equals
--   $$\pi\,\Gamma_{\mathbb{R}}\bigl(c(P)+c(P_2)+2s+n+1\bigr)\,(-\varepsilon')^{n}\,(-1)^{a_{w_0}^{\sharp}+m}\,2^{m}\,(2\pi)^{-(s+u_P+u_{w_0}+m/2)}\,\Gamma\bigl(s+u_P+u_{w_0}+\tfrac m2\bigr)\cdot 2\rho\,\Gamma\bigl(s+u_P+\mu+\tfrac{m+k}{2}\bigr)(4\pi)^{-(s+u_P+\mu+\frac{m+k}{2})}.$$
--   Here $u_{w_0}=u^{\mathbb{R}}_{w_0}$ and $a_{w_0}=a^{\mathbb{R}}_{w_0}$ are the archimedean data of $\mu$ at $w_0$, with $a_{w_0}^{\sharp}$ its integer lift; $\chi_{u,a}(y)=|y|^{u}$ multiplied by $1$ if $a=0$ and by $\mathrm{sign}(y)$ otherwise; $W_r$ is $W_r(\mathrm{par}_0)$ at the default place of $\mathbb{Q}$; $\mathcal{W}_D$ is $D$'s Whittaker function and $\mathrm{diag}(y,1)$ the matrix $\begin{pmatrix}y&0\\0&1\end{pmatrix}$; $c(P)=2u_P$ and $c(P_2)=2\mu$ are the central exponents, so the exponent of $y$ is $2u_P+2\mu+2s$; and $I_y(e)$ is the Godement inner integral
--   $$I_y(e)=\int_{v\in\mathbb{R}^2} S\Bigl(e\cdot\bigl[\,\delta_{0b}+v_0\delta_{2b}\,;\,\delta_{1b}+v_1\delta_{2b}\,\bigr]_{b}\Bigr)\,\psi_\infty\bigl(y\cdot(-v_1)\bigr)\,dv,$$
--   the rows being formed from the $3\times3$ identity matrix as in `godementInner3` with third argument $1$, and the character being $\psi_\infty$ shifted by the diagonal infinite adele with all coordinates $y$.
--
--   This is the closed-form evaluation of the unfolded archimedean (primal) torus pair occurring in the Rankin–Selberg/Godement integral for the cubic induction, on the branch where both the $GL_2$ profile over $\mathbb{Q}$ and the Levi datum $D$ are discrete series of weights $m=n_P+1$ and $k$, and the section is the harmonic Gaussian $S$ of bidegree $(m,n)$. It refines `exists_forall_unfoldedTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3`, in which the pair is expressed as a constant times the torus transform of $\mathcal{W}_D$, by inserting the explicit discrete-series profiles and computing the remaining Laplace–Mellin integral; it feeds the archimedean gamma-factor identity `exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_oneComplex_discreteLevi` used in the converse-theorem step of Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_discreteLevi_ed2.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_discreteLevi_ed2
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
            (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
              = (Real.pi : ℂ) * Complex.Gammaℝ (P.centralExponent + P₂.centralExponent + 2 * s + (n : ℂ) + 1) *
              ((-(ε' : ℂ)) ^ n) * (-1 : ℂ) ^ ((aR w₀ h₀).val + m) * (2 : ℂ) ^ m *
              (2 * (Real.pi : ℂ)) ^ (-(s + uP + uR w₀ h₀ + (m : ℂ) / 2)) * Complex.Gamma (s + uP + uR w₀ h₀ + (m : ℂ) / 2) *
              (ρ * (2 : ℂ) * Complex.Gamma (s + uP + μ + ((m : ℂ) + (k : ℂ)) / 2) * (4 * (Real.pi : ℂ)) ^ (-(s + uP + μ + ((m : ℂ) + (k : ℂ)) / 2))) := by sorry
