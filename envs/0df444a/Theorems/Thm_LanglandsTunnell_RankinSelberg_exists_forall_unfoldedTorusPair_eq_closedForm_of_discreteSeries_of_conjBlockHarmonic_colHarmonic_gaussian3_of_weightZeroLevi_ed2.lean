-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_weightZeroLevi_ed2
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_weightZeroLevi_ed2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/f68f1d2b-7ea1-583a-8c23-fab10ef6ed77
-- title:
--   Closed form of the unfolded torus pair: weight-zero Levi branch
-- statement:
--   The setting is a number field $K$ of degree $3$ over $\mathbb{Q}$, with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, and an idele class character $\mu : (\mathbb{A}_K)^{\times} \to \mathbb{C}^{\times}$.
--
--   **Global frame.** The hypothesis `_hμ` says that $\mu$ is an *admissible twist*: it is trivial on the principal ideles coming from $K^{\times}$, continuous, and unitary ($|\mu(x)| = 1$ for all $x$). The hypothesis `_hns` excludes the possibility that $\mu$ comes from $\mathbb{Q}$: there is no admissible twist $\eta$ of $\mathbb{Q}$ with $\mu(\varpi_{\mathfrak{P}}) = \eta(\varpi_{\mathfrak{p}})^{f(\mathfrak{P}/\mathfrak{p})}$, where $\mathfrak{p} = \mathfrak{P} \cap \mathcal{O}_{\mathbb{Q}}$, for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified and with $\eta$ unramified at $\mathfrak{p}$; here $\varpi_v$ denotes the idele `uniformizerIdele` concentrated at $v$, $f$ is `inertiaDeg'`, and 'unramified at $v$' means that the local component of the character is trivial on the units of the local integers. The archimedean components of $\mu$ are parametrised by $u_{\mathbb{R}}(w), a_{\mathbb{R}}(w) \in \mathbb{C} \times \mathbb{Z}/2$ at real places and $u_{\mathbb{C}}(w) \in \mathbb{C}$, $k_{\mathbb{C}}(w) \in \mathbb{Z}$ at complex places, the hypotheses `huR`, `huC` asserting in each case the relation `IsArchCompAt`, namely that the local character of $\mu$ at $w$ sends a unit $x$ of the completion to $\|x\|^{\mathrm{mult}(w) \cdot u} \cdot (\iota_w(x)/\|x\|)^{a}$, with $a = (a_{\mathbb{R}}(w))$ lifted to $\mathbb{Z}$, resp. $a = k_{\mathbb{C}}(w)$. A character $\omega$ of the ideles of $\mathbb{Q}$ is given together with `hω`, a conjunction of three clauses: $\omega$ is an admissible twist; at every prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ which is not a *bad place* for $(K,\mu)$ — that is, $p$ is unramified in $K$ and $\mu$ is unramified at every prime above $p$ — the character $\omega$ is unramified and $\omega(\varpi_p)$ equals `inducedE3`, minus the degree-$3$ coefficient of the induced Euler polynomial formed from the local coefficients `inducedCoeff K μ` (which are $\mu(\varpi_{\mathfrak{P}})$ at unramified $\mathfrak{P}$ and $0$ otherwise); and, for every choice of archimedean parameters satisfying the two relations above and every real place $v$ of $\mathbb{Q}$, the archimedean component of $\omega$ at $v$ has exponent $\sum_{w \text{ real}} u_{\mathbb{R}}(w) + \sum_{w \text{ complex}} 2u_{\mathbb{C}}(w)$ and integer parameter $\sum_{w \text{ real}} (a_{\mathbb{R}}(w)) + \sum_{w \text{ complex}} (k_{\mathbb{C}}(w)+1)$ (finite sums). Further global data: a splitting $E$ of the infinite ideles into the full idele group, with `hE` saying that $E(u)$ has infinite part $u$ and trivial finite part; a rational number $a$, nonzero and equal to $-1$, a unit $a_\infty$ of the infinite adele ring whose underlying element is the image of $a$; an additive character $\psi_\infty$ of the infinite adele ring with $\psi_\infty(x) = \psi_{\mathrm{arch}}(a x)$ for the standard archimedean character `psiArch`; measurable and Borel structures on the infinite adele ring and its unit group; an additive measure $\nu_{\mathrm{add}}$ equal to $|a|^{1/2}$ times the pushforward of Lebesgue measure along the inverse of the identification of the infinite adele ring with the mixed space; and a Haar measure $\nu_{\mathrm{mul}}$ on the infinite idele units.
--
--   **Archimedean $\mathrm{GL}_2$ profile at the place of $\mathbb{Q}$.** A real archimedean parameter $P$ is given (either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u_0,k)$ with $k \ge 1$), subject to `_hP₁`: in the principal case $|\mathrm{Re}(u_1-u_2)| < 1$. Data $kw : \mathbb{Z}/2 \times \mathrm{InfinitePlace}(\mathbb{Q}) \to \mathbb{Z}$, $W_r : \mathbb{Z}/2 \times \mathrm{InfinitePlace}(\mathbb{Q}) \to (\mathbb{R} \to \mathbb{C})$ and $W_A : \mathbb{Z}/2 \to (\mathrm{GL}_2(\mathbb{R}) \to \mathbb{C})$ satisfy: `hkw1`, in the principal case $kw(\mathrm{par},w) = \mathrm{signShift}(a_1+\mathrm{par}) + \mathrm{signShift}(a_2+\mathrm{par})$ (where $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$); `hkw2`, in the discrete case $kw(\mathrm{par},w) = k+1$; `hWr1`, when $P = \mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par} = a_1$, the parity law $W_r(\mathrm{par},w)(-t) = (-1)^{a_1} W_r(\mathrm{par},w)(t)$; `hWr2`, in the discrete case $W_r(\mathrm{par},w)$ vanishes on $t<0$; `hWr3`, when $P = \mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par} = a_1+1$, existence of an abscissa beyond which the Mellin transform of $t \mapsto (W_r(\mathrm{par},w)(t) + (-1)^{a_1}W_r(\mathrm{par},w)(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P$ twisted by $(0,a_1)$; `hWr4`, for every $b$ equal to $\mathrm{par}$ or to $\mathrm{par} +$ the central sign of $P$, existence of an abscissa beyond which the same Mellin transform (with $b$ in place of $a_1$) converges and equals the archimedean factor of $P$ twisted by $(0,b)$. The function $W_A$ obeys the Whittaker laws: `hWAN`, $W_A(\mathrm{par})(n(x)h) = e^{-2\pi i a x} W_A(\mathrm{par})(h)$ for the unipotent $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$; `hWAZ`, $W_A(\mathrm{par})(z \cdot h) = |z|^{c(P)+1}(z/|z|)^{\varepsilon(P)} W_A(\mathrm{par})(h)$ for scalar $z$, with $c(P)$ the central exponent and $\varepsilon(P)$ the central sign of $P$; `hWAK`, right equivariance $W_A(\mathrm{par})(h\kappa) = \mathrm{archWeightChar}_{\mathbb{R}}(kw(\mathrm{par},\mathrm{default}))(\kappa) \, W_A(\mathrm{par})(h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt`, $W_A(\mathrm{par})(\mathrm{diag}(t,1)) = W_r(\mathrm{par},\mathrm{default})(t)$ for $t \in \mathbb{R}^{\times}$; and `hWAc`, continuity of each $W_A(\mathrm{par})$. An element $w_{0\mathbb{R}} \in \mathrm{GL}_2(\mathbb{R})$ with matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ is also given.
--
--   **Levi datum.** A real place $w_0$ of $K$ is fixed, together with a real archimedean parameter $P_2$ and the shape hypothesis `hP₂`: either there are two further real places $w_1 \ne w_2$ of $K$, both distinct from $w_0$, with $\{w_0,w_1,w_2\}$ exhausting the infinite places of $K$, and $P_2 = \mathrm{principal}(u_{\mathbb{R}}(w_1), a_{\mathbb{R}}(w_1), u_{\mathbb{R}}(w_2), a_{\mathbb{R}}(w_2))$; or there is a complex place $w_C$ with $\{w_C, w_0\}$ exhausting the infinite places and either $k_{\mathbb{C}}(w_C) \ne 0$ and $P_2 = \mathrm{discrete}(u_{\mathbb{C}}(w_C), |k_{\mathbb{C}}(w_C)|)$, or $k_{\mathbb{C}}(w_C) = 0$ and $P_2 = \mathrm{principal}(u_{\mathbb{C}}(w_C),0,u_{\mathbb{C}}(w_C),1)$. The datum $D$ is an `ArchDatumR P₂`: a function $D.W$ on $2\times 2$ real matrices, smooth on the locus of nonzero determinant, with the unipotent law $D.W(n(x)g) = \psi(x)D.W(g)$, the central law $D.W(zg) = \chi_{P_2}(z)|z| D.W(g)$ for $z \ne 0$, and, summarised here, an entire completion `zetaEntire` of its torus zeta integrals against quasicharacters, valid beyond an abscissa, together with the functional equation carrying the epsilon factor of the twist, a finite-order bound in vertical strips, and decay bounds for the iterated derivatives for large and for small torus variable. An integer $k_0$ is given with `hDW`, right equivariance of $D.W$ of weight $k_0$ under `rowIsometrySubgroup₀ ℝ`; `hDE`, the Casimir eigenvalue equation $\mathrm{matrixCasimir}(D.W)(x) = \lambda(P_2) D.W(x)$ for $\det x \ne 0$, with $\lambda(\mathrm{principal}(u_1,\cdot,u_2,\cdot)) = 1/4 - ((u_1-u_2)/2)^2$ and $\lambda(\mathrm{discrete}(\cdot,k)) = (1-k^2)/4$; `hDnz`, $D.W \not\equiv 0$; and `hk₀min`, stating that if $P_2$ is principal with signs $a_1,a_2$ then $k_0 \in \{0,1\}$ and $k_0 \equiv a_1+a_2 \bmod 2$, while if $P_2 = \mathrm{discrete}(u,m)$ then $k_0 = m+1$.
--
--   **Branch specialisation.** Here $P = \mathrm{discrete}(u_P,n_P)$ with $n_P \ge 1$ and $m = n_P+1$; consequently those clauses above that are conditioned on $P$ being a principal-series parameter (`_hP₁`, `hkw1`, `hWr1`, `hWr3`) are vacuous. Natural numbers $n$ and a real $\varepsilon'$ satisfy `hcol`: either $\varepsilon' = -1$ and $n = k_0 - m$, or $\varepsilon' = 1$ and $n = m - k_0$. A parity $\mathrm{par}_0 \in \mathbb{Z}/2$ is fixed, and the flat section $S$ on $2 \times 3$ real matrices is given by
--   $$S(M) = \bigl((M_{00} - i M_{10}) - i(M_{01} - iM_{11})\bigr)^m \, (M_{02} + \varepsilon' i M_{12})^n \, e^{-\pi \sum_{i,b} M_{ib}^2}.$$
--   The profile of $W_r$ at the parity $\mathrm{par}_0$ and the unique archimedean place of $\mathbb{Q}$ is explicit: $W_r(\mathrm{par}_0)(t) = 2 t^{u_P + n_P/2 + 1} e^{-2\pi t}$ for $t>0$ (`hWpos`) and $W_r(\mathrm{par}_0)(t) = 0$ for $t < 0$ (`hWneg`). Finally $k_0 = 0$, $P_2 = \mathrm{principal}(\mu_1,c,\mu_2,c)$ for some $\mu_1,\mu_2 \in \mathbb{C}$ and $c \in \mathbb{Z}/2$, and for some $\rho \in \mathbb{C}$ the torus profile of $D$ is, by `hD`,
--   $$D.W\bigl(\mathrm{diag}(\tau,1)\bigr) = \rho\,\tau \cdot 4\int_0^{\infty} r^{\mu_1} e^{-\pi r^2} \cdot (\tau/r)^{\mu_2} e^{-\pi (\tau/r)^2} \, \frac{dr}{r} \qquad (\tau > 0).$$
--   (With $k_0 = 0$ and $m \ge 2$ the first alternative of `hcol` cannot hold, so $\varepsilon' = 1$ and $n = m$.)
--
--   **Conclusion.** There exists $\sigma_a \in \mathbb{R}$ such that for every $s \in \mathbb{C}$ with $\mathrm{Re}\,s > \sigma_a$ the following identity holds, the outer integral being over $e \in \mathbb{R}^{2\times 2}$ with respect to Lebesgue measure:
--   $$\int_{e} q\bigl(u_{\mathbb{R}}(w_0)+2,\ a_{\mathbb{R}}(w_0)\bigr)(\det e)\;|\det e|^{-2}\; T(s,e)\; Y(s,e)\; de \;=\; R(s),$$
--   where $q(u,\alpha)(y) = |y|^{u}$ if $\alpha = 0$ and $|y|^{u}\,\mathrm{sign}(y)$ otherwise, and
--   $$T(s,e) = \int_{\mathbb{R}} W_r(\mathrm{par}_0)(t)\; D.W\bigl(\mathrm{diag}(a t,1)\cdot e^{-1}\bigr)\; |t|^{\,s-1/2}\; t^{-2}\, dt,$$
--   $$Y(s,e) = \int_0^{\infty} y^{\,c(P)+c(P_2)+2s}\; \mathrm{godementInner3}\bigl(\psi_\infty \text{ shifted by } \iota(y),\, S,\, e,\, 1\bigr)\, dy,$$
--   the last integrand being $\int_{v \in \mathbb{R}^2} S\bigl(e \cdot (\text{the } 2\times 3 \text{ matrix with rows } \delta_{0b} + v_0\delta_{2b},\, \delta_{1b}+v_1\delta_{2b})\bigr)\, \psi_\infty\bigl(\iota(y)\cdot \iota(-v_1)\bigr)$ for the third matrix argument equal to the identity, with $\iota(y)$ the image of $y$ in the infinite adele ring under `ofReal`; and
--   $$R(s) = \pi\,\Gamma_{\mathbb{R}}\bigl(c(P)+c(P_2)+2s+n+1\bigr)\,(-\varepsilon')^{n}\,(-1)^{a_{\mathbb{R}}(w_0)+m}\,2^{m}\,(2\pi)^{-\left(s+u_P+u_{\mathbb{R}}(w_0)+\frac{m}{2}\right)}\,\Gamma\Bigl(s+u_P+u_{\mathbb{R}}(w_0)+\tfrac{m}{2}\Bigr)$$
--   $$\times\; \rho\cdot 2\cdot B\Bigl(s+u_P+\tfrac{m}{2}+\mu_1,\; s+u_P+\tfrac{m}{2}+\mu_2\Bigr)\,\Gamma_{\mathbb{R}}\Bigl(2\bigl(s+u_P+\tfrac{m}{2}\bigr)+\mu_1+\mu_2\Bigr),$$
--   where $c(P) = 2u_P$ and $c(P_2) = \mu_1+\mu_2$ are the central exponents of $P$ and $P_2$, $\Gamma_{\mathbb{R}}(z) = \pi^{-z/2}\Gamma(z/2)$, $B$ is the beta integral, and $(-1)^{a_{\mathbb{R}}(w_0)}$ uses the representative in $\{0,1\}$.
--
--   This is the archimedean 'primal torus pair' computation in the Rankin–Selberg/Godement unfolding of the cubic-induction converse theorem: it evaluates the unfolded torus integral in closed form for a discrete-series parameter at the archimedean place of $\mathbb{Q}$, a weight-zero principal-series Levi datum ($k_0 = 0$, $P_2 = \mathrm{principal}(\mu_1,c,\mu_2,c)$) and the harmonic flat section built from the Gaussian on $2 \times 3$ matrices. It relies on the general unfolding identity `exists_forall_unfoldedTorusPair_eq_const_mul_setIntegral_W_diagOne_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3` together with the Laplace–Mellin evaluation `setIntegral_mulConvGaussian_mul_cpow_mul_exp_eq_betaIntegral_mul_GammaR`, and feeds the assembly of the archimedean gamma factor in `exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_threeReal_sameSign`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_weightZeroLevi_ed2.lean

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
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_closedForm_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3_of_weightZeroLevi_ed2
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
              (ρ * (2 : ℂ) * Complex.betaIntegral (s + uP + (m : ℂ) / 2 + μ₁) (s + uP + (m : ℂ) / 2 + μ₂) *
                Complex.Gammaℝ (2 * (s + uP + (m : ℂ) / 2) + μ₁ + μ₂)) := by sorry
