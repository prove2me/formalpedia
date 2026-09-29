-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/b880fe66-1832-5a38-8d4f-5b040be2b88e
-- title:
--   Integrability of the unfolded archimedean torus-pair integrand
-- statement:
--   The setting is a cubic field with a twisting character and the archimedean data attached to it.
--
--   **Field and character data.** $K$ is a number field whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, with $\mathrm{finrank}_{\mathbb{Q}} K = 3$ (`_hdeg`), and $\mu : (\mathbb{A}_K)^{\times} \to \mathbb{C}^{\times}$ is a monoid homomorphism on the idele units. The hypothesis `_hμ` asserts `IsAdmissibleTwist K μ`, i.e. $\mu$ is trivial on the principal ideles coming from $K^{\times}$, is continuous, and has values of absolute value $1$. The hypothesis `_hns` asserts that $\mu$ is not obtained from $\mathbb{Q}$: there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every height-one prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified (its local character is trivial on the units of the valuation ring) and at whose prime $p = \mathfrak{P}\cap\mathcal{O}_{\mathbb{Q}}$ below $\eta$ is unramified, one has $\mu(\varpi_{\mathfrak{P}}) = \eta(\varpi_{p})^{f(\mathfrak{P}/p)}$, where $\varpi$ denotes the uniformizer idele and $f$ the inertia degree `inertiaDeg'`.
--
--   **Archimedean components of $\mu$.** Functions $uR, aR$ on the real places and $uC, kC$ on the complex places of $K$ (with values in $\mathbb{C}$, $\mathbb{Z}/2$, $\mathbb{C}$, $\mathbb{Z}$ respectively) are given, and `huR`, `huC` assert `IsArchCompAt`: at each real place $w$ the local component of $\mu$ on $(K_w)^{\times}$ is $x \mapsto \|x\|^{\,\mathrm{mult}(w)\,uR(w)}\,(x/\|x\|)^{(aR(w)).\mathrm{val}}$, and at each complex place $w$ it is $x \mapsto \|x\|^{\,\mathrm{mult}(w)\,uC(w)}(x/\|x\|)^{kC(w)}$.
--
--   **The character $\omega$ over $\mathbb{Q}$.** $\omega : (\mathbb{A}_{\mathbb{Q}})^{\times}\to\mathbb{C}^{\times}$, and `hω` consists of three clauses: $\omega$ is an admissible twist of $\mathbb{Q}$; at every prime $p$ of $\mathcal{O}_{\mathbb{Q}}$ which is not a bad place for $(K,\mu)$ — that is, $p$ is unramified in $K$ and $\mu$ is unramified at every prime of $K$ above $p$ — the character $\omega$ is unramified at $p$ and its Euler coefficient $\omega(\varpi_p)$ equals `inducedE3 ℚ (inducedCoeff K μ) p`, minus the coefficient of degree $3$ of the induced Euler polynomial formed from the unramified Frobenius values of $\mu$; and, for every choice of data $uR, aR, uC, kC$ satisfying the two `IsArchCompAt` conditions above, the archimedean component of $\omega$ at the real place $v$ of $\mathbb{Q}$ is given by `IsArchCompAt ℚ ω v` with exponent $\sum_{w\ \mathrm{real}} uR(w) + \sum_{w\ \mathrm{complex}} 2\,uC(w)$ and integer parameter $\sum_{w\ \mathrm{real}} (aR(w)).\mathrm{val} + \sum_{w\ \mathrm{complex}} (kC(w)+1)$, the sums being finite sums (`finsum`) over the places in question.
--
--   **Splitting of the infinite part.** $E$ is a monoid homomorphism from $(\mathbb{A}_{\mathbb{Q},\infty})^{\times}$ to $(\mathbb{A}_{\mathbb{Q}})^{\times}$ with `hE`: for every $u$, the infinite part of $E(u)$ is $u$ and the finite part of $E(u)$ is $1$.
--
--   **Additive datum and measures.** $a\in\mathbb{Q}$ with $a \neq 0$ (`ha`) and $a = -1$ (`ha1`); $a_{\infty}$ is a unit of the infinite adele ring whose underlying element is the image of $a$ (`haInf`); $\psi_{\infty}$ is the additive character $x\mapsto \psi_{\mathrm{arch}}(a\,x)$, where $\psi_{\mathrm{arch}}$ is the standard archimedean character of $\mathbb{A}_{\mathbb{Q},\infty}$ (`hpsiInf`). A measure $\nu_{\mathrm{add}}$ on the infinite adele ring is required to equal $|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the identification of $\mathbb{A}_{\mathbb{Q},\infty}$ with the mixed space (`hν_add`), and $\nu_{\mathrm{mul}}$ is a Haar measure on $(\mathbb{A}_{\mathbb{Q},\infty})^{\times}$.
--
--   **The parameter $P$ and the Whittaker data over $\mathbb{Q}$.** $P$ is a real archimedean parameter, either `principal u₁ a₁ u₂ a₂` or `discrete u n hn`, subject to `_hP₁`: in the principal case $|\mathrm{Re}(u_1-u_2)| < 1$. Functions $kw : \mathbb{Z}/2 \to \mathrm{InfinitePlace}\,\mathbb{Q}\to\mathbb{Z}$, $Wr : \mathbb{Z}/2 \to \mathrm{InfinitePlace}\,\mathbb{Q}\to\mathbb{C}\to\mathbb{C}$ and $WA : \mathbb{Z}/2\to \mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$ are given with the following hypotheses, for each parity `par` and each real place $w$ of $\mathbb{Q}$: `hkw1`, in the principal case, $kw(\mathrm{par},w) = \mathrm{signShift}(a_1+\mathrm{par}) + \mathrm{signShift}(a_2+\mathrm{par})$ with $\mathrm{signShift}(0)=0$, $\mathrm{signShift}(1)=1$; `hkw2`, in the discrete case with parameter $n$, $kw(\mathrm{par},w) = n+1$; `hWr1`, if $P = \mathrm{principal}\,u_1\,a_1\,u_2\,a_1$ and $\mathrm{par}=a_1$ then $Wr(\mathrm{par},w,-t) = (-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w,t)$ for all real $t$; `hWr2`, in the discrete case $Wr(\mathrm{par},w,t)=0$ for $t<0$; `hWr3`, if $P = \mathrm{principal}\,u_1\,a_1\,u_2\,a_1$ and $\mathrm{par}=a_1+1$, there is an abscissa beyond which the Mellin transform of $t\mapsto (Wr(\mathrm{par},w,t) + (-1)^{a_1.\mathrm{val}}Wr(\mathrm{par},w,-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}\,(P.\mathrm{twist}\,0\,a_1).\mathrm{archFactor}(s)$; `hWr4`, for $b = \mathrm{par}$ or $b = \mathrm{par} + P.\mathrm{centralSign}$, there is an abscissa beyond which the same Mellin transform with $b$ in place of $a_1$ converges and equals $(P.\mathrm{twist}\,0\,b).\mathrm{archFactor}(s)$. The function $WA$ satisfies: `hWAN`, $WA(\mathrm{par},n(x)h) = e^{-2\pi i a x}\,WA(\mathrm{par},h)$ for the unipotent $n(x) = \binom{1\ \ x}{0\ \ 1}$; `hWAZ`, $WA(\mathrm{par}, z\cdot h) = |z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{(P.\mathrm{centralSign}).\mathrm{val}}\,WA(\mathrm{par},h)$ for scalar matrices $z$; `hWAK`, $WA(\mathrm{par},h\kappa) = \mathrm{archWeightChar}_{\mathbb{R}}(kw(\mathrm{par},\mathrm{default}))(\kappa)\,WA(\mathrm{par},h)$ for $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ`; `hWAt`, $WA(\mathrm{par},\mathrm{diag}(t,1)) = Wr(\mathrm{par},\mathrm{default},t)$ for units $t$ of $\mathbb{R}$, `default` being the infinite place of $\mathbb{Q}$; `hWAc`, each $WA(\mathrm{par},\cdot)$ is continuous.
--
--   **Places of $K$ and the parameter $P_2$.** $w_{0R}\in\mathrm{GL}_2(\mathbb{R})$ has matrix $\binom{0\ \ 1}{1\ \ 0}$ (`hw₀R`); $w_0$ is a real place of $K$ (`h₀`). $P_2$ is a real archimedean parameter, and `hP₂` requires one of two alternatives: either there are two further distinct real places $w_1,w_2$ of $K$, different from $w_0$, such that $w_0,w_1,w_2$ exhaust the infinite places and $P_2 = \mathrm{principal}\,(uR\,w_1)\,(aR\,w_1)\,(uR\,w_2)\,(aR\,w_2)$; or there is a complex place $w_C$ such that $w_C,w_0$ exhaust the infinite places and either $kC(w_C)\neq 0$ and $P_2 = \mathrm{discrete}\,(uC\,w_C)\,|kC(w_C)|$, or $kC(w_C)=0$ and $P_2 = \mathrm{principal}\,(uC\,w_C)\,0\,(uC\,w_C)\,1$.
--
--   **The archimedean datum $D$ and the Schwartz function.** $D$ is an `ArchDatumR P₂`, that is a function $W$ on $2\times 2$ real matrices, smooth on the invertible ones, with the unipotent and central transformation laws for $P_2$, together with an entire completion of its zeta integrals, integrability of the zeta integrand to the right of an abscissa, the identity expressing the zeta integral as $(P_2.\mathrm{twist}\,u\,a).\mathrm{archFactor}(s)$ times that completion, the local functional equation with the epsilon factor of $P_2$, finite order in vertical strips, and the decay estimates along the torus at infinity and at zero. An integer $k_0$ is given with `hDW`: $D.W(x\kappa) = \mathrm{archWeightChar}_{\mathbb{R}}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`: $D$ is a Casimir eigenfunction, $\mathrm{matrixCasimir}(D.W)(x) = P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all $x$ with $\det x\neq 0$; and `hDnz`: $D.W$ does not vanish identically on $\mathrm{GL}_2(\mathbb{R})$. Finally $S$ belongs to `polyGauss3`, i.e. $S(M) = p\big((M_{ib})\big)\exp\big(-\pi\sum_{i,b}M_{ib}^2\big)$ for some polynomial $p$ in the six matrix entries with complex coefficients, $M$ running over real $2\times 3$ matrices; and $\mathrm{par}_0 \in \mathbb{Z}/2$.
--
--   **Conclusion.** There exists $\sigma_u\in\mathbb{R}$ such that for every $s\in\mathbb{C}$ with $\mathrm{Re}\,s > \sigma_u$ the function of $p = (y,t,M) \in \mathbb{R}\times\mathbb{R}\times(\mathrm{Fin}\,2\to\mathrm{Fin}\,2\to\mathbb{R})$, with $e$ the matrix determined by $M$, given by
--   $$\mathrm{quasiChar}\big(uR(w_0)+2,\;aR(w_0)\big)(\det e)\cdot |\det e|^{-2}\cdot\Big(Wr(\mathrm{par}_0,\mathrm{default},t)\cdot D.W\big(\mathrm{diag}(a t,1)\,e^{-1}\big)\cdot |t|^{\,s-1/2}\cdot t^{-2}\Big)\cdot\Big(y^{\,P.\mathrm{centralExponent}+P_2.\mathrm{centralExponent}+2s}\cdot \mathrm{godementInner3}\big(\psi_{\infty}\ \text{shifted by the image of } y,\,S,\,e,\,1\big)\Big)$$
--   is integrable for the product of Lebesgue measure restricted to $(0,\infty)$ in the variable $y$ with Lebesgue measure on $\mathbb{R}$ in the variable $t$ and Lebesgue measure on the four matrix entries. Here $\mathrm{quasiChar}(u,\alpha)(z) = |z|^{u}$ times $1$ if $\alpha = 0$ and times $\mathrm{sign}(z)$ otherwise, $\mathrm{diag}(y,1)$ denotes `ArchR.diagOne`, and the last factor is the Godement inner integral $\int_{\mathbb{R}^2} S\big(e\cdot\binom{1\ \ 0\ \ v_0}{0\ \ 1\ \ v_1}\big)\,\psi_{\infty}\big(y\cdot(-v_1)\big)\,dv$, the shift and the argument of the character being taken through the embedding of $\mathbb{R}$ into $\mathbb{A}_{\mathbb{Q},\infty}$.
--
--   This is the analytic domination step for the archimedean unfolding of the Rankin–Selberg integral attached to a cubic induction: it provides joint absolute integrability, in a right half-plane in $s$, of the integrand obtained by unfolding the torus pairing of the Jacquet vector against the archimedean Whittaker datum $D$. It is used by [`LanglandsTunnell.RankinSelberg.exists_forall_torusPair_jacquetVector3_eq_integral_quasiChar_mul_torusIntegral_mul_godementMellin`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_torusPair_jacquetVector3_eq_integral_quasiChar_mul_torusIntegral_mul_godementMellin), where the integrability licenses the application of Fubini's theorem and the change of variables that separate the torus integral from the Godement–Mellin factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3
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
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) (par₀ : ZMod 2) :
    ∃ σu : ℝ, ∀ s : ℂ, σu < s.re →
      MeasureTheory.Integrable
        (fun p : ℝ × ℝ × (Fin 2 → Fin 2 → ℝ) =>
          ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of p.2.2).det *
              (((|(Matrix.of p.2.2).det| ^ 2)⁻¹ : ℝ) : ℂ) *
            (Wr par₀ default p.2.1 * D.W (ArchR.diagOne ((a : ℝ) * p.2.1) * (Matrix.of p.2.2)⁻¹) *
                (((|p.2.1| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((p.2.1 ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((p.1 : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
              godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal p.1)) S (Matrix.of p.2.2) 1))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
            (MeasureTheory.volume : MeasureTheory.Measure (Fin 2 → Fin 2 → ℝ)))) := by sorry
