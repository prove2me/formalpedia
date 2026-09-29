-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_setIntegral_dualConfig_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.dualTorusPair_eq_setIntegral_dualConfig_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/22584b03-fdce-5f57-96ba-7f181bdc0cce
-- title:
--   Dual torus pair unfolded for a quadratic Schwartz section
-- statement:
--   The setting is the archimedean frame of the cubic-induction Rankin–Selberg computation over $\mathbb{Q}$, with the following data.
--
--   Field and character data. A number field $K$, equipped with an integral $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_K$, with $\operatorname{finrank}_{\mathbb{Q}} K = 3$ (hypothesis `_hdeg`); a character $\mu\colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ which is an admissible twist, i.e. trivial on the image of $K^\times$, continuous and of absolute value $1$ everywhere (`_hμ`); the hypothesis `_hns`, asserting that there is no admissible twist $\eta$ of $\mathbb{Q}$ such that for every $\mathfrak{P}\in\operatorname{Spec}^1(\mathcal{O}_K)$ at which $\mu$ is unramified and with $\eta$ unramified at the place $p$ below, $\mu$ evaluated at the uniformiser idele of $\mathfrak{P}$ equals $\eta$ at the uniformiser idele of $p$ raised to the inertia degree of $\mathfrak{P}$ over $p$.
--
--   Archimedean components of $\mu$. Functions $u_R, a_R$ on the real places and $u_C, k_C$ on the complex places of $K$ (with values in $\mathbb{C}$, $\mathbb{Z}/2$, $\mathbb{C}$, $\mathbb{Z}$ respectively), together with `huR` and `huC`: for each real place $w$ the local character of $\mu$ at $w$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,u_R(w)}\,(x/\|x\|)^{a_R(w).\mathrm{val}}$, and for each complex place $w$ it is $x\mapsto \|x\|^{\mathrm{mult}(w)\,u_C(w)}\,(x/\|x\|)^{k_C(w)}$.
--
--   The companion character over $\mathbb{Q}$. A character $\omega\colon(\mathbb{A}_{\mathbb{Q}})^\times\to\mathbb{C}^\times$ and the three-clause hypothesis `hω`: $\omega$ is an admissible twist; at every finite place $p$ of $\mathbb{Q}$ which is not a bad place for $(K,\mu)$ (i.e. neither ramified in $K$ nor twist-ramified above), $\omega$ is unramified and its Euler coefficient equals $\operatorname{inducedE3}$ of the induced coefficients of $\mu$ at $p$, namely minus the degree-$3$ coefficient of the induced Euler polynomial; and, for every choice of archimedean data $u_R,a_R,u_C,k_C$ satisfying the two conditions above, at every real place $v$ of $\mathbb{Q}$ the local character of $\omega$ is given by the exponent $\sum_{w\ \mathrm{real}} u_R(w) + \sum_{w\ \mathrm{complex}} 2u_C(w)$ and the integer $\sum_{w\ \mathrm{real}} a_R(w).\mathrm{val} + \sum_{w\ \mathrm{complex}} (k_C(w)+1)$.
--
--   Splitting, base point and additive character. A monoid homomorphism $E\colon (\mathbb{A}_{\mathbb{Q},\infty})^\times \to (\mathbb{A}_{\mathbb{Q}})^\times$ with, for every $u$, infinite part $u$ and finite part $1$ (`hE`); a rational number $a$ with $a\neq 0$ and $a=-1$ (`ha`, `ha1`); a unit $a_\infty$ of the infinite adeles whose underlying element is the image of $a$ (`haInf`); an additive character $\psi_\infty$ of $\mathbb{A}_{\mathbb{Q},\infty}$ with $\psi_\infty(x)=\psi_{\mathrm{arch}}(a x)$ for all $x$, where $\psi_{\mathrm{arch}}$ is the standard archimedean additive character (`hpsiInf`).
--
--   Measures. A measure $\nu_{\mathrm{add}}$ on $\mathbb{A}_{\mathbb{Q},\infty}$ equal to $|a|^{1/2}$ times the push-forward of Lebesgue measure under the inverse of the identification of the infinite adeles with the mixed space (`hν_add`), and a Haar measure $\nu_{\mathrm{mul}}$ on $(\mathbb{A}_{\mathbb{Q},\infty})^\times$.
--
--   The real archimedean parameter and its Whittaker family. A parameter $P : \mathrm{RealArchParam}$ with `_hP₁`: if $P = \mathrm{principal}(u_1,a_1,u_2,a_2)$ then $|\Re(u_1-u_2)|<1$. Families $k_w\colon \mathbb{Z}/2\times \mathrm{InfinitePlace}(\mathbb{Q})\to\mathbb{Z}$, $W_r\colon \mathbb{Z}/2\times\mathrm{InfinitePlace}(\mathbb{Q})\to(\mathbb{C}\to\mathbb{C})$ and $W_A\colon\mathbb{Z}/2\to (\mathrm{GL}_2(\mathbb{R})\to\mathbb{C})$, subject to: `hkw1`, `hkw2`, fixing the weight ($k_w(\mathrm{par},w)=\mathrm{signShift}(a_1+\mathrm{par})+\mathrm{signShift}(a_2+\mathrm{par})$ in the principal case, $k_w(\mathrm{par},w)=n+1$ in the discrete case of weight $n$); `hWr1`, `hWr2`, the reflection law $W_r(\mathrm{par},w)(-t)=(-1)^{a_1.\mathrm{val}}W_r(\mathrm{par},w)(t)$ in the even principal case with $\mathrm{par}=a_1$, and vanishing on $t<0$ in the discrete case; `hWr3`, `hWr4`, two Mellin-transform identities: for $\Re s$ large the Mellin transform of $t\mapsto (W_r(\mathrm{par},w)(t)+(-1)^{b.\mathrm{val}}W_r(\mathrm{par},w)(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}\,(P.\mathrm{twist}\,0\,a_1).\mathrm{archFactor}(s)$ in the case $P=\mathrm{principal}(u_1,a_1,u_2,a_1)$, $\mathrm{par}=a_1+1$, $b=a_1$ of `hWr3`, and equals $(P.\mathrm{twist}\,0\,b).\mathrm{archFactor}(s)$ whenever $b=\mathrm{par}$ or $b=\mathrm{par}+P.\mathrm{centralSign}$; and the transformation laws `hWAN` (unipotent: $W_A(\mathrm{par})(u(x)h)=e^{-2\pi i a x}W_A(\mathrm{par})(h)$), `hWAZ` (central: $W_A(\mathrm{par})(z\,h)=|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{P.\mathrm{centralSign}.\mathrm{val}}W_A(\mathrm{par})(h)$ for scalar $z$), `hWAK` (right transformation under the subgroup `rowIsometrySubgroup₀ ℝ` by the character `archWeightCharℝ (kw par default)`), `hWAt` ($W_A(\mathrm{par})(\mathrm{diag}(t,1))=W_r(\mathrm{par},\mathrm{default})(t)$) and `hWAc` (continuity of each $W_A(\mathrm{par})$).
--
--   The reflection element and the place $w_0$. An element $w_{0R}\in\mathrm{GL}_2(\mathbb{R})$ with underlying matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and a real place $w_0$ of $K$.
--
--   The complementary parameter and its Whittaker datum. A parameter $P_2$ with `hP₂`: either there are two further real places $w_1\neq w_2$, both distinct from $w_0$, exhausting the infinite places of $K$, and $P_2=\mathrm{principal}(u_R(w_1),a_R(w_1),u_R(w_2),a_R(w_2))$; or there is a complex place $w_C$ such that $w_C,w_0$ exhaust the infinite places and either $k_C(w_C)\neq 0$ and $P_2=\mathrm{discrete}(u_C(w_C),|k_C(w_C)|)$, or $k_C(w_C)=0$ and $P_2=\mathrm{principal}(u_C(w_C),0,u_C(w_C),1)$. An archimedean Whittaker datum $D$ of type $P_2$ and an integer $k_0$ with: `hDW`, $D.W(x\kappa)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(\kappa)\,D.W(x)$ for $\kappa$ in `rowIsometrySubgroup₀ ℝ`; `hDE`, $D$ is a Casimir eigenfunction, i.e. $\mathrm{matrixCasimir}(D.W)(x)=P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all invertible $x$; `hDnz`, $D.W$ does not vanish identically; and `hk₀min`, requiring $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2 \bmod 2$ in the principal case for $P_2$, and $k_0=m+1$ in the discrete case of weight $m$.
--
--   Specialisation of the frame. Complex numbers $\nu_1,\nu_2$ and $b\in\mathbb{Z}/2$ with `hPev`: $P=\mathrm{principal}(\nu_1,b,\nu_2,b)$ (so $P.\mathrm{centralSign}=0$ and $P.\mathrm{centralExponent}=\nu_1+\nu_2$); `hk₀`: $k_0=0$; `hLevi`: in the principal case $P_2=\mathrm{principal}(u_1,a_1,u_2,a_2)$ one has $a_1=b+1$; an integer $\delta\in\{0,1\}$ with $\delta \equiv a_R(w_0)+b \bmod 2$ (`hδ`, `hδpar`).
--
--   The section. A function $S$ on real $2\times 3$ matrices given by
--   $$S(M)=(M_{00}M_{11}-M_{01}M_{10})^{\delta}\,\big((M_{00}+iM_{10})^2+(M_{01}+iM_{11})^2\big)\,(M_{02}-iM_{12})^2\, e^{-\pi\sum_{i,j}M_{ij}^2},$$
--   the last factor being `gaussian3` (`hS`). Finally a complex number $s$.
--
--   Under all of these hypotheses, the following identity of iterated integrals holds. Write $q=\begin{pmatrix}a_1&0\\0&a_2\end{pmatrix}$ for the element [`AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂`](def/AutomorphicForm_SiegelCoordinates.html#L126) of $\mathrm{GL}_2(\mathbb{R})$, so $|\det q|=|a_1a_2|$, and let $\rho_j=(e^{-1})_{1j}$ denote the second row of the inverse of a matrix $e\in M_2(\mathbb{R})$.
--
--   The left-hand side is $\int_{a_2\in(0,\infty)}\int_{a_1\in\mathbb{R}}$ of the integrand which is $0$ unless $a_1\neq 0$ and $a_2>0$, and in that case equals
--   $$\Big(|\det q|\cdot W_A(b)\big(w_{0R}\cdot{}^{t}q^{-1}\big)\cdot \Lambda\big(\mathrm{arch}_3(\iota(\,q\ \text{at the real place of }\mathbb{Q}))\big)\Big)\cdot|\det q|^{\,s-1/2}\cdot (a_1^{2})^{-1},$$
--   where ${}^{t}q^{-1}$ is [`RSCarrier.transposeInv q`](def/LanglandsTunnell_RSCarrier.html#L31), the argument of $\Lambda$ is the archimedean component of the image of $q$ under the block embedding $\mathrm{GL}_2\hookrightarrow\mathrm{GL}_3$ of the adelic groups composed with the embedding of $\mathrm{GL}_2(\mathbb{R})$ at the unique real place of $\mathbb{Q}$, and $\Lambda$ is the dual Whittaker function $\Lambda(g)=J(w_3\cdot{}^{t}g^{-1})$ attached, through `dualWhittakerFn3` with $w_3$ the $3\times 3$ antidiagonal permutation matrix `longWeyl3`, to the Jacquet vector $J=\mathrm{jacquetVector3}\,D\,u_R(w_0)\,a_R(w_0)\,a\,\psi_\infty\,S$, itself the product of $\mathrm{quasiChar}(u_R(w_0)+1,a_R(w_0))$ of the determinant of the real matrix of $g$ with the integral over $e\in M_2(\mathbb{R})$ of `jacquetIntegrand3`.
--
--   The right-hand side is $\int_{a_2\in(0,\infty)}\int_{a_1\in\mathbb{R}}$ of the integrand which is again $0$ unless $a_1\neq 0$ and $a_2>0$, and otherwise is the product of four factors: first
--   $$|a_1a_2|\cdot\Big(i^{\,k_w(b,\mathrm{default})}\cdot\big(|-a_1^{-1}|^{\,P.\mathrm{centralExponent}+1}\,\big((-a_1^{-1})/|-a_1^{-1}|\big)^{P.\mathrm{centralSign}.\mathrm{val}}\big)\cdot W_r(b,\mathrm{default})(-a_1/a_2)\Big);$$
--   second the product of $\mathrm{quasiChar}(u_R(w_0)+1,a_R(w_0))\big(-(a_1a_2)^{-1}\big)$ with
--   $$\int_{e\in M_2(\mathbb{R})}\Big[(e_{00}-ie_{10})^2\,e^{-\pi\left(a_2^{-2}(e_{01}^2+e_{11}^2)+(e_{00}^2+e_{10}^2)\right)}\cdot \frac{a_1^{2}}{|\det e|}\cdot B(e)\cdot e^{-\pi a^2a_1^2(\rho_0^2+\rho_1^2)}\Big]\times$$
--   $$\times\ \mathrm{quasiChar}(u_R(w_0)+2,a_R(w_0))(\det e)\cdot |\det e|^{-2}\cdot D.W\big(\mathrm{diag}(a,1)\,e^{-1}\big)\,de,$$
--   where the bracket $B(e)$ is
--   $$\big(-i\,a\,a_1\,a_2^{-1}(e_{11}\rho_0-e_{01}\rho_1)\big)^{\delta}\Big(\big(a_2^{-1}(e_{01}+ie_{11})\big)^2-\big(a\,a_1(\rho_0+i\rho_1)\big)^2\Big)-\delta\,\frac{\big(a_2^{-1}(e_{01}+ie_{11})\big)\big(a\,a_1(\rho_0+i\rho_1)\big)}{\pi};$$
--   third the factor $|a_1a_2|^{\,s-1/2}$; and fourth $(a_1^{2})^{-1}$. Here $\mathrm{quasiChar}(u,\alpha)(y)=|y|^{u}$ if $\alpha=0$ and $|y|^{u}\operatorname{sign}(y)$ otherwise, and $\mathrm{diag}(a,1)$ is the matrix $\begin{pmatrix}a&0\\0&1\end{pmatrix}$.
--
--   This is the dual (reflected) half of the archimedean torus computation in the Rankin–Selberg unfolding for the cubic induction: the $\mathrm{GL}_2$-Whittaker reflection factor is separated from the $\mathrm{GL}_3$ Jacquet vector, and the inner $v$-integral of the Jacquet vector is replaced by its closed form for the section $\det^{\delta}\cdot(z_0^2+z_1^2)\cdot(M_{02}-iM_{12})^2\cdot$ Gaussian, leaving an explicit double integral over the torus coordinates $(a_1,a_2)$ against an integral over $M_2(\mathbb{R})$. It is used by the statement that the dual torus pair equals the archimedean root number times an explicit expression times the gamma factor in this frame.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_setIntegral_dualConfig_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3.lean

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

theorem LanglandsTunnell.RankinSelberg.dualTorusPair_eq_setIntegral_dualConfig_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3
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
    (s : ℂ) :
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA b (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
      = (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                ((((|a₁ * a₂| : ℝ) : ℂ) *
                    (Complex.I ^ (kw b default) *
                      ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
                        ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) *
                      Wr b default (-a₁ / a₂))) *
                  (ArchR.quasiChar (uR w₀ h₀ + 1) (aR w₀ h₀) (-(a₁ * a₂)⁻¹) *
                    ∫ e : Fin 2 → Fin 2 → ℝ,
                      ((((e 0 0 : ℝ) : ℂ) - Complex.I * ((e 1 0 : ℝ) : ℂ)) ^ 2 *
                    (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (e 0 1 ^ 2 + e 1 1 ^ 2) + (e 0 0 ^ 2 + e 1 0 ^ 2)))) : ℂ) *
                    (((a₁ ^ 2 * |(Matrix.of e).det|⁻¹ : ℝ)) : ℂ) *
                    ((-Complex.I * ((a : ℂ) * (a₁ : ℂ) * (a₂⁻¹ : ℂ) * (((e 1 1 : ℝ) : ℂ) * (((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) - ((e 0 1 : ℝ) : ℂ) * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)))) ^ δ *
              (((a₂⁻¹ : ℂ) * (((e 0 1 : ℝ) : ℂ) + Complex.I * ((e 1 1 : ℝ) : ℂ))) ^ 2 - ((a : ℂ) * (a₁ : ℂ) * ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) + Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ))) ^ 2) -
            (δ : ℂ) * ((a₂⁻¹ : ℂ) * (((e 0 1 : ℝ) : ℂ) + Complex.I * ((e 1 1 : ℝ) : ℂ))) * ((a : ℂ) * (a₁ : ℂ) * ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) + Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ))) / (Real.pi : ℂ)) *
                    (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * a₁ ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ)) *
                        (ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)) *
                        D.W (ArchR.diagOne (a : ℝ) * (Matrix.of e)⁻¹)) *
                  (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0) := by sorry
