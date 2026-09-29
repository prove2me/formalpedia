-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightOne_profile
-- name    : LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightOne_profile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/19af4265-b4d7-5c8a-9b7e-56841e705be8
-- title:
--   Dual archimedean torus pair, weight-one Levi branch
-- statement:
--   The setting is a cubic number field and an admissible twist of it, together with a complete archimedean package. Fix a number field $K$ with $\mathrm{finrank}_{\mathbb Q} K = 3$ (hypothesis `_hdeg`), with $\mathcal O_K$ an integral $\mathcal O_{\mathbb Q}$-algebra, and a homomorphism $\mu$ from the ideles of $K$ to $\mathbb C^\times$ which is an admissible twist, i.e. trivial on $K^\times$, continuous and unitary (`_hμ`). The hypothesis `_hns` is the non-descent condition: there is no admissible twist $\eta$ of $\mathbb Q$ such that for every $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified and $\eta$ is unramified at the prime $p$ below $\mathfrak P$ one has $\mu(\varpi_{\mathfrak P}) = \eta(\varpi_p)^{f}$, $f$ the inertia degree of $\mathfrak P$ over $p$.
--
--   The archimedean parameters of $\mu$ are recorded by families $uR, aR$ at the real places and $uC, kC$ at the complex places of $K$, with values in $\mathbb C$, $\mathbb Z/2$, $\mathbb C$, $\mathbb Z$ respectively; `huR` and `huC` state that for each place $w$ the archimedean local component of $\mu$ at $w$ is $x \mapsto \|x\|^{\,\mathrm{mult}(w)\,u}\,(x/\|x\|)^{a}$ with $(u,a) = (uR\,w, (aR\,w).\mathrm{val})$ at a real place and $(u,a) = (uC\,w, kC\,w)$ at a complex place.
--
--   Further data: a homomorphism $\omega$ from the ideles of $\mathbb Q$ to $\mathbb C^\times$ subject to the three-clause hypothesis `hω`, namely ($\alpha$) $\omega$ is an admissible twist of $\mathbb Q$; ($\beta$) at every prime $p$ which is neither ramified in $K$ nor twist-ramified above (i.e. `¬ IsBadPlace K μ p`), $\omega$ is unramified and its Euler coefficient $\omega(\varpi_p)$ equals $-$(coefficient of degree $3$ in the induced Euler polynomial of the coefficient system $\mathfrak P \mapsto \mu(\varpi_{\mathfrak P})$); ($\gamma$) for every choice of archimedean data for $\mu$ as above and every real place $v$ of $\mathbb Q$, the archimedean component of $\omega$ at $v$ has exponent $\sum_{w \text{ real}} uR\,w + \sum_{w \text{ complex}} 2\,uC\,w$ and weight $\sum_{w \text{ real}} (aR\,w).\mathrm{val} + \sum_{w \text{ complex}} (kC\,w + 1)$. A homomorphism $E$ from the units of the infinite adeles of $\mathbb Q$ into the ideles splits the infinite part: `hE` says the infinite part of $E\,u$ is $u$ and its finite part is $1$. A rational number $a$ is assumed non-zero and equal to $-1$ (`ha`, `ha1`), $a_\infty$ is an infinite-adelic unit with image $a$ (`haInf`), and $\psi_\infty$ is the additive character $x \mapsto \psi_{\mathrm{arch}}(a x)$ (`hpsiInf`). Measurable and Borel structures on the infinite adeles and their units are assumed; $\nu_{\mathrm{add}}$ is the measure $|a|^{1/2}$ times the transport of Lebesgue measure along the inverse of the mixed-space ring isomorphism (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on the units.
--
--   The $\mathrm{GL}_2(\mathbb R)$ Whittaker package is carried by a real archimedean parameter $P$ with `_hP₁` ($|\mathrm{Re}(u_1-u_2)| < 1$ whenever $P = \mathrm{principal}\,u_1 a_1 u_2 a_2$), by weights $kw$, torus functions $Wr$ and group functions $WA$, all indexed by a parity $\mathrm{par} \in \mathbb Z/2$. The weight clauses are `hkw1` ($kw\,\mathrm{par}\,w = \mathrm{signShift}(a_1+\mathrm{par}) + \mathrm{signShift}(a_2+\mathrm{par})$ in the principal case) and `hkw2` ($kw\,\mathrm{par}\,w = n+1$ in the discrete case of weight $n$). The torus clauses are `hWr1` (in the even principal case $P = \mathrm{principal}\,u_1 a_1 u_2 a_1$ with $\mathrm{par} = a_1$: $Wr(-t) = (-1)^{a_1.\mathrm{val}} Wr(t)$), `hWr2` (in the discrete case $Wr$ vanishes on $t<0$), `hWr3` (in the even principal case with $\mathrm{par} = a_1+1$ there is $s_0$ such that for $\mathrm{Re}\,s > s_0$ the Mellin transform of $t \mapsto (Wr\,\mathrm{par}\,w\,t + (-1)^{a_1.\mathrm{val}} Wr\,\mathrm{par}\,w\,(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}\,(P.\mathrm{twist}\,0\,a_1).\mathrm{archFactor}(s)$), and `hWr4` (for $b$ equal to $\mathrm{par}$ or to $\mathrm{par} + P.\mathrm{centralSign}$, the corresponding Mellin transform converges and equals $(P.\mathrm{twist}\,0\,b).\mathrm{archFactor}(s)$ on a right half-plane). The group clauses are `hWAN` (unipotent equivariance with character $x \mapsto \exp(-2\pi i a x)$), `hWAZ` (central equivariance: $WA(\mathrm{scalar}(z)h) = |z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{(P.\mathrm{centralSign}).\mathrm{val}}\,WA(h)$), `hWAK` (right equivariance under the row-isometry subgroup by the character $\mathrm{archWeightChar}_{\mathbb R}(kw\,\mathrm{par}\,\mathrm{default})$), `hWAt` ($WA\,\mathrm{par}(\mathrm{diag}(t,1)) = Wr\,\mathrm{par}\,\mathrm{default}\,t$) and `hWAc` (continuity). Finally $w_{0R} \in \mathrm{GL}_2(\mathbb R)$ is the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ (`hw₀R`).
--
--   On the $K$-side, $w_0$ is a real place of $K$ and $P_2$ a real archimedean parameter subject to `hP₂`, which offers the two shapes of the archimedean profile of a cubic field: either $K$ has three distinct real places $w_0, w_1, w_2$ exhausting all infinite places and $P_2 = \mathrm{principal}(uR\,w_1, aR\,w_1, uR\,w_2, aR\,w_2)$; or $K$ has one complex place $w_C$ besides $w_0$, and $P_2 = \mathrm{discrete}(uC\,w_C, |kC\,w_C|)$ when $kC\,w_C \ne 0$, respectively $P_2 = \mathrm{principal}(uC\,w_C, 0, uC\,w_C, 1)$ when $kC\,w_C = 0$. Attached to $P_2$ is an archimedean datum $D$ (a Whittaker function $D.W$ on $2\times 2$ real matrices with the smoothness, unipotent and central laws, zeta integrals, functional equation, finite order and decay bundled into `ArchDatumR`) and an integer $k_0$, with: `hDW`, right equivariance $D.W(x r) = \mathrm{archWeightChar}_{\mathbb R}(k_0)(r)\,D.W(x)$ for $r$ in the row-isometry subgroup; `hDE`, that $D$ is a Casimir eigenfunction with eigenvalue $P_2.\mathrm{laplaceEigenvalue}$; `hDnz`, that $D.W$ is not identically zero; and `hk₀min`, that $k_0 \in \{0,1\}$ with $k_0 \equiv a_1 + a_2 \pmod 2$ in the principal case for $P_2$, and $k_0 = m+1$ in the discrete case of weight $m$.
--
--   The parameter $P$ is of even principal type: $P = \mathrm{principal}\,\nu_1\,b\,\nu_2\,b$ (`hPev`), and `hLevi` requires $a_1 = b$ in the principal case for $P_2$ whenever $k_0 = 0$. Integers $n$ with $(n : \mathbb Z) = k_0$ (`hn`) and $\delta \in \{0,1\}$ (`hδ`) with $\delta \equiv aR\,w_0 + b \pmod 2$ (`hδpar`) govern the Schwartz section $S$ on $2\times 3$ real matrices, which by `hS` is
--   $$S(M) = (M_{00}M_{11} - M_{01}M_{10})^{\delta}\,(M_{02} - i M_{12})^{n}\,\mathrm{gaussian3}(M), \qquad \mathrm{gaussian3}(M) = e^{-\pi \sum_{i,b} M_{ib}^2}.$$
--
--   The branch hypotheses single out the weight-one Levi case: $P_2 = \mathrm{principal}\,u_1\,c_1\,u_2\,c_2$ (`hP₂eq`) with $c_1 \ne c_2$ (`hc`) and $k_0 = 1$ (`hk₀`), and a constant $\rho \in \mathbb C$ realising the torus profile of $D$ (`hρ`): for every $b' \in \mathbb Z/2$ and every $\tau > 0$,
--   $$D.W(\mathrm{diag}(\tau,1)) + (-1)^{b'.\mathrm{val}} D.W(\mathrm{diag}(-\tau,1)) = \rho\,\tau\cdot 4\int_0^\infty r^{\,u_1 + \mathrm{signShift}(c_1+b')} e^{-\pi r^2}\,(\tau/r)^{\,u_2 + \mathrm{signShift}(c_2+b')} e^{-\pi (\tau/r)^2}\,\frac{dr}{r}.$$
--
--   Conclusion: there exists $\sigma_a \in \mathbb R$ such that for every $s$ with $\mathrm{Re}\,s > \sigma_a$ the dual unfolded torus pair
--   $$\int_{a_2 > 0}\int_{a_1 \in \mathbb R} F_s(a_1,a_2)\,da_1\,da_2$$
--   is evaluated, where $F_s(a_1,a_2) = 0$ unless $a_1 \ne 0$ and $a_2 > 0$, in which case, with $q = \begin{pmatrix}a_1 & 0\\ 0 & a_2\end{pmatrix} \in \mathrm{GL}_2(\mathbb R)$,
--   $$F_s(a_1,a_2) = |\det q|\cdot WA\,b\,\bigl(w_{0R}\,(q^{-1})^{\mathsf T}\bigr)\cdot \Bigl(\mathrm{dualWhittakerFn3}\,\bigl(\mathrm{jacquetVector3}\,D\,(uR\,w_0)\,(aR\,w_0)\,a\,\psi_\infty\,S\bigr)\Bigr)(g_q)\cdot |\det q|^{\,s - 1/2}\cdot a_1^{-2},$$
--   $g_q$ being the archimedean component of the image of $q$ under the inclusion of $\mathrm{GL}_2(\mathbb R)$ at the archimedean place of $\mathbb Q$ followed by the embedding $\mathrm{GL}_2 \hookrightarrow \mathrm{GL}_3$ of the cubic induction, and $\mathrm{dualWhittakerFn3}\,W(g) = W(w_3\,(g^{-1})^{\mathsf T})$ with $w_3$ the long Weyl element of $\mathrm{GL}_3$. The value of this double integral is asserted to be
--   $$\Bigl(\varepsilon_\infty\cdot(-1)^{(P.\mathrm{centralSign}).\mathrm{val}}\cdot(-1)^{\#\{w \text{ complex}\}}\Bigr)\cdot\Bigl((-1)^{b.\mathrm{val}}\,\frac{\pi}{2}\,\rho\Bigr)\cdot\Gamma^\vee(s),$$
--   where $\varepsilon_\infty = \mathrm{archRootNumber}\,K$ formed from the constant families $w \mapsto P$ at the real places and $w \mapsto P.\mathrm{baseChange}$ at the complex places, twisted by $uR, aR, uC, kC$, and where
--   $$\Gamma^\vee(s) = \prod_{x \in \mathrm{twistedGammaR}} \Gamma_{\mathbb R}\bigl(s + \tfrac12 + x\bigr)\cdot\prod_{x \in \mathrm{twistedGammaC}} \Gamma_{\mathbb C}\bigl(s + \tfrac12 + x\bigr),$$
--   the two multisets being $\mathrm{twistedGammaR}\,K$ and $\mathrm{twistedGammaC}\,K$ formed from the dualised constant families $w \mapsto P^\vee$ and $w \mapsto (P.\mathrm{baseChange})^\vee$, twisted by the negated exponents $-uR$, $-uC$ and the weights $aR$, $-kC$.
--
--   This is the dual half of the archimedean $\mathrm{GL}(3)\times\mathrm{GL}(2)$ Rankin–Selberg torus computation at the real place of $\mathbb Q$, in the branch where the $\mathrm{GL}(2)$ Levi datum is principal with distinct sign parameters and of weight $k_0 = 1$: the unfolded dual torus integral against the long-Weyl transform of the Jacquet vector of the explicit section $(\det)^\delta(M_{02}-iM_{12})^n$ times a Gaussian is identified with the archimedean root number times the explicit constant $(-1)^{b}\tfrac{\pi}{2}\rho$ times the dual twisted $\Gamma$-product. It feeds the combined primal-and-dual torus-pair statement [`LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3), which supplies the archimedean input to the converse theorem used in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightOne_profile.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_colHarmonic_gaussian3_of_weightOne_profile
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

    (u₁ u₂ : ℂ) (c₁ c₂ : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c₁ u₂ c₂) (hc : c₁ ≠ c₂) (hk₀ : k₀ = 1)
    (ρ : ℂ)
    (hρ : ∀ (b' : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b'.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁ + signShift (c₁ + b')) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (u₂ + signShift (c₂ + b')) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ))) :
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
