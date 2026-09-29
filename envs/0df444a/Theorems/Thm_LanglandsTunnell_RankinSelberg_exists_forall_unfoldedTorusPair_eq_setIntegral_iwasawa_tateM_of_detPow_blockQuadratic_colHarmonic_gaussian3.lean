-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_detPow_blockQuadratic_colHarmonic_gaussian3
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_detPow_blockQuadratic_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/4439e2ba-61be-562c-b7ad-ff56bcd7f1c5
-- title:
--   Iwasawa form of the unfolded torus pair, quadratic-block Gaussian datum
-- statement:
--   The setting is that of the archimedean Rankin–Selberg analysis attached to a cubic field and an induced character, and the hypotheses fall into the following groups.
--
--   **Field and twist.** $K$ is a number field whose ring of integers is integral over $\mathbb{Z}$, with $\operatorname{finrank}_{\mathbb Q} K = 3$ (hypothesis `_hdeg`), and $\mu \colon (\mathbb A_K)^\times \to \mathbb C^\times$ is an admissible twist (`_hμ`): it is trivial on the principal ideles, continuous, and of absolute value $1$. The hypothesis `_hns` asserts that $\mu$ does not descend: there is no admissible twist $\eta$ of $\mathbb Q$ such that for every $\mathfrak P \in \operatorname{HeightOneSpectrum}(\mathcal O_K)$ at which $\mu$ is unramified (its local character is trivial on the units of the local integers) and at which $\eta$ is unramified at the prime below, the value of $\mu$ on the idele `uniformizerIdele K 𝔓` (a uniformiser at $\mathfrak P$, trivial elsewhere) equals the corresponding value of $\eta$ at the prime below, raised to the inertia degree `inertiaDeg'` of $\mathfrak P$ over it.
--
--   **Archimedean components of $\mu$.** Functions `uR`, `aR` on the real places and `uC`, `kC` on the complex places of $K$ are given, with values in $\mathbb C$, $\mathbb Z/2$, $\mathbb C$, $\mathbb Z$ respectively, and `huR`, `huC` assert that at each place $w$ the archimedean local component of $\mu$ is $x \mapsto \|x\|^{\,m_w \cdot u} \,(\iota_w(x)/\|x\|)^{a}$, with $(u,a) = (\mathtt{uR}\,w, (\mathtt{aR}\,w).\mathrm{val})$ at real $w$ and $(u,a) = (\mathtt{uC}\,w, \mathtt{kC}\,w)$ at complex $w$.
--
--   **The induced character $\omega$ on $\mathbb Q$.** $\omega \colon (\mathbb A_{\mathbb Q})^\times \to \mathbb C^\times$ satisfies the three clauses of `hω`: $\omega$ is an admissible twist; at every prime $p$ of $\mathbb Q$ which is not a bad place for $(K,\mu)$ (that is, $p$ is unramified in $K$ and $\mu$ is unramified at every prime of $K$ above $p$), $\omega$ is unramified at $p$ and its Euler coefficient (the value of $\omega$ at the uniformiser idele at $p$) equals `inducedE3 ℚ (inducedCoeff K μ) p`, minus the degree-$3$ coefficient of the induced Euler polynomial built from the unramified values of $\mu$; and, for every choice of archimedean data for $\mu$ as above, at each real place $v$ of $\mathbb Q$ the archimedean component of $\omega$ has exponent $\sum_{w\ \mathrm{real}} \mathtt{uR}\,w + \sum_{w\ \mathrm{complex}} 2\,\mathtt{uC}\,w$ and integer parameter $\sum_{w\ \mathrm{real}} (\mathtt{aR}\,w).\mathrm{val} + \sum_{w\ \mathrm{complex}} (\mathtt{kC}\,w + 1)$ (finite sums over the places).
--
--   **Splitting of the infinite part.** $E$ is a monoid homomorphism from the infinite ideles of $\mathbb Q$ to the ideles such that, for every $u$, the infinite part of $E u$ is $u$ and its finite part is $1$ (`hE`).
--
--   **The additive datum and the measures.** $a \in \mathbb Q$ with $a \neq 0$ and $a = -1$; `aInf` is the infinite idele that is the image of $a$; $\psi_\infty$ is the additive character $x \mapsto \psi_{\mathrm{arch}}(a x)$, where $\psi_{\mathrm{arch}}$ is the standard archimedean character of $\mathbb Q$. Borel measurable structures on the infinite adeles and on their unit group are fixed; $\nu_{\mathrm{add}}$ is $|a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the identification of the infinite adeles with the mixed space, and $\nu_{\mathrm{mul}}$ is a Haar measure on the unit group.
--
--   **The real archimedean parameter $P$ and the associated Whittaker data.** $P$ is a `RealArchParam`, so either $\mathrm{principal}(u_1,a_1,u_2,a_2)$ or $\mathrm{discrete}(u_0,n_0)$ with $n_0 \ge 1$; `_hP₁` requires $|\mathrm{Re}(u_1-u_2)| < 1$ in the principal case. Data $kw$ (integer weights), $W_r$ (functions on $\mathbb R$) and $W_A$ (functions on $GL_2(\mathbb R)$), all indexed by a parity in $\mathbb Z/2$, are given, subject to: `hkw1`, `hkw2`, fixing the weight as $\mathrm{signShift}(a_1+\mathrm{par}) + \mathrm{signShift}(a_2+\mathrm{par})$ in the principal case and $n_0+1$ in the discrete case; `hWr1`, the parity law $W_r(-t) = (-1)^{a_1.\mathrm{val}} W_r(t)$ when $P = \mathrm{principal}(u_1,a_1,u_2,a_1)$ and $\mathrm{par} = a_1$; `hWr2`, vanishing of $W_r$ on $t<0$ in the discrete case; `hWr3`, which in the principal case with $a_2 = a_1$ and $\mathrm{par} = a_1+1$ provides an abscissa beyond which the Mellin transform of $t \mapsto (W_r(t) + (-1)^{a_1.\mathrm{val}} W_r(-t))/t$ converges and equals $\frac{2s+u_1+u_2-1}{4\pi}$ times the archimedean factor of $P.\mathrm{twist}\,0\,a_1$ at $s$; `hWr4`, which for $b = \mathrm{par}$ or $b = \mathrm{par} + P.\mathrm{centralSign}$ gives an abscissa beyond which the same Mellin transform, with $(-1)^{b.\mathrm{val}}$ in place of $(-1)^{a_1.\mathrm{val}}$, converges and equals the archimedean factor of $P.\mathrm{twist}\,0\,b$ at $s$; and the Whittaker laws for $W_A$: `hWAN`, equivariance under the unipotent $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ by $e^{-2\pi i a x}$; `hWAZ`, equivariance under the scalar matrix of $z \in \mathbb R^\times$ by $|z|^{P.\mathrm{centralExponent}+1}(z/|z|)^{(P.\mathrm{centralSign}).\mathrm{val}}$; `hWAK`, right equivariance under `rowIsometrySubgroup₀ ℝ` by the character `archWeightCharℝ (kw par default)`; `hWAt`, the restriction $W_A(\mathrm{diag}(t,1)) = W_r\,\mathrm{par}\,\mathrm{default}\,t$; and `hWAc`, continuity of each $W_A\,\mathrm{par}$. The element $w_{0R} \in GL_2(\mathbb R)$ is the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   **The distinguished real place and the second parameter.** $w_0$ is a real place of $K$, and $P_2$ is a `RealArchParam` subject to the profile hypothesis `hP₂`: either $K$ has exactly three places, $w_0$ and two further distinct real places $w_1,w_2$, and $P_2 = \mathrm{principal}(\mathtt{uR}\,w_1, \mathtt{aR}\,w_1, \mathtt{uR}\,w_2, \mathtt{aR}\,w_2)$; or $K$ has exactly the places $w_0$ and one complex place $w_C$, and then either $\mathtt{kC}\,w_C \neq 0$ and $P_2 = \mathrm{discrete}(\mathtt{uC}\,w_C, |\mathtt{kC}\,w_C|)$, or $\mathtt{kC}\,w_C = 0$ and $P_2 = \mathrm{principal}(\mathtt{uC}\,w_C, 0, \mathtt{uC}\,w_C, 1)$.
--
--   **The archimedean Whittaker datum $D$.** $D$ is an `ArchDatumR P₂`: a function $D.W$ on $2\times 2$ real matrices, smooth on the locus of invertible matrices, with the unipotent law $D.W(\mathrm{unip}(x)g) = \psi(x) D.W(g)$ and the central law $D.W(zg) = \mathrm{centralChar}(P_2)(z)\,|z|\,D.W(g)$ for $z \neq 0$, together with an entire zeta function satisfying the prescribed integral representation by $\int \mathrm{zetaIntegrand}$, a functional equation with the epsilon factor of the twisted parameter, finite order in vertical strips, and the decay bounds for iterated derivatives at large and small $|y|$. An integer $k_0$ is given with: `hDW`, right equivariance of $D.W$ under `rowIsometrySubgroup₀ ℝ` by `archWeightCharℝ k₀`; `hDE`, that $D$ is a Casimir eigenvector, i.e. $\mathrm{matrixCasimir}(D.W)(x) = P_2.\mathrm{laplaceEigenvalue}\cdot D.W(x)$ for all $x$ with $\det x \neq 0$; `hDnz`, that $D.W$ is not identically zero on $GL_2(\mathbb R)$; and `hk₀min`, that $k_0 \in \{0,1\}$ with $k_0 \equiv a_1 + a_2 \bmod 2$ in the principal case, and $k_0 = m+1$ in the discrete case $\mathrm{discrete}(u,m)$.
--
--   **The Schwartz datum.** A parity $\mathrm{par}_0 \in \mathbb Z/2$, natural numbers $n$ and $\delta$ with $\delta \in \{0,1\}$, and a sign $\varepsilon' = \pm 1$ are fixed, and $S$ on $2\times 3$ real matrices is given by
--   $$S(M) = (M_{00}M_{11}-M_{01}M_{10})^{\delta}\,\bigl((M_{00}+iM_{10})^2 + (M_{01}+iM_{11})^2\bigr)\,(M_{02}+\varepsilon' i M_{12})^{n}\, e^{-\pi \sum_{i,b} M_{ib}^2}.$$
--
--   **Conclusion.** There exists $\sigma_1 \in \mathbb R$ such that for every $s \in \mathbb C$ with $\mathrm{Re}\,s > \sigma_1$,
--   $$\int_{e \in M_2(\mathbb R)} \mathrm{quasiChar}(u_{w_0}+2, a_{w_0})(\det e)\;|\det e|^{-2}\;\Bigl(\int_{\mathbb R} W_r(\mathrm{par}_0, \mathrm{default}, t)\, D.W(\mathrm{diag}(at,1)\,e^{-1})\,|t|^{s-1/2}\,t^{-2}\,dt\Bigr)\Bigl(\int_{y>0} y^{\,c(P)+c(P_2)+2s}\,\mathrm{godementInner3}\bigl(\psi_\infty\text{ shifted by }\mathrm{ofReal}(y)\bigr)(S)(e)(1)\,dy\Bigr)\,de$$
--   equals the integral over $(x,y_1,y_2,\theta) \in \mathbb R \times \mathbb R \times (0,\infty) \times (0,2\pi]$ of
--   $$\mathrm{quasiChar}(u_{w_0}+2,a_{w_0})\bigl((y_1y_2)^{-1}\bigr)\,\bigl|(y_1y_2)^{-1}\bigr|^{-2}\;\Bigl(\int_{\mathbb R} W_r(\mathrm{par}_0,\mathrm{default},t)\,D.W(\mathrm{diag}(at,1)\,g)\,|t|^{s-1/2}\,t^{-2}\,dt\Bigr)\cdot \mathcal M \cdot \frac{y_2^2}{|y_1y_2|^4},$$
--   where $u_{w_0} = \mathtt{uR}\,w_0$, $a_{w_0} = \mathtt{aR}\,w_0$, $c(P)$ and $c(P_2)$ are the central exponents of $P$ and $P_2$, $\mathrm{quasiChar}(u,\alpha)(y) = |y|^{u}$ times $\mathrm{sign}(y)$ if $\alpha \neq 0$ and times $1$ if $\alpha = 0$,
--   $$g = \begin{pmatrix} y_1\cos\theta + x y_2 \sin\theta & -y_1\sin\theta + x y_2\cos\theta \\ y_2\sin\theta & y_2\cos\theta\end{pmatrix},$$
--   and the explicit factor $\mathcal M$ is
--   $$(y_1y_2)^{-\delta}\,\Bigl[(\cos\theta - i\sin\theta)^2\Bigl(\frac{1+x^2}{y_1^2}-\frac{1}{y_2^2} - i\,\frac{2x}{y_1y_2}\Bigr)\Bigr]\, e^{-\pi\left(\frac{1+x^2}{y_1^2}+\frac{1}{y_2^2}\right)}\,|y_1y_2|\,(-ia)^n\,(y_2\sin\theta + \varepsilon' i\, y_2\cos\theta)^n\cdot \tfrac12\,\bigl(\pi a^2((y_2\sin\theta)^2+(y_2\cos\theta)^2)\bigr)^{-\frac{c(P)+c(P_2)+2s+n+1}{2}}\,\Gamma\Bigl(\frac{c(P)+c(P_2)+2s+n+1}{2}\Bigr).$$
--   Here $\mathrm{godementInner3}(\psi)(S)(h)(m) = \int_{v \in \mathbb R^2} S\bigl(h\cdot[\,m_{0\bullet}+v_0 m_{2\bullet};\ m_{1\bullet}+v_1 m_{2\bullet}\,]\bigr)\,\psi(\mathrm{ofReal}(-v_1))\,dv$, and $\mathrm{ofReal}(y)$ denotes the infinite adele with component $y$ at every place. The data entering the two sides are $s$, $\mathtt{uR}\,w_0$, $\mathtt{aR}\,w_0$, $W_r(\mathrm{par}_0,\mathrm{default},\cdot)$, $D.W$, $a$, $n$, $\delta$, $\varepsilon'$, the central exponents of $P$ and $P_2$, and $\psi_\infty$; the remaining hypotheses fix the ambient arithmetic and archimedean frame.
--
--   This is the unfolding step, in Iwasawa coordinates, of the primal torus integral attached to the Jacquet vector of the Schwartz datum $\det(\text{block})^{\delta}\,(z_0^2+z_1^2)\,(\text{column harmonic})^n\,\times$ Gaussian: the integral over $M_2(\mathbb R)$ is rewritten as an integral over $(x,y_1,y_2,\theta)$ with Jacobian $y_2^2|y_1y_2|^{-4}$, and simultaneously the inner Godement integral over $y>0$ is replaced by its closed-form Gamma evaluation. It feeds the computation of the unfolded torus pair as an explicit multiple of a gamma factor in the even principal case with column harmonic of degree two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_detPow_blockQuadratic_colHarmonic_gaussian3.lean

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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

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

theorem LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_detPow_blockQuadratic_colHarmonic_gaussian3
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
    (par₀ : ZMod 2) (n δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (ε' : ℝ) (hε' : ε' = 1 ∨ ε' = -1)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) ^ 2 + (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ)) ^ 2) *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M) :
    ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
      (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
        = ∫ p : ℝ × ℝ × ℝ × ℝ in Set.univ ×ˢ (Set.univ ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi))),
            (let x : ℝ := p.1
             let y₁ : ℝ := p.2.1
             let y₂ : ℝ := p.2.2.1
             let θ : ℝ := p.2.2.2
             let g : Matrix (Fin 2) (Fin 2) ℝ :=
               !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
                  y₂ * Real.sin θ, y₂ * Real.cos θ]
             ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (y₁ * y₂)⁻¹ *
                 (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
               ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * g) *
                   (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                (((((y₁ * y₂)⁻¹ : ℝ) : ℂ)) ^ δ *
                  ((((Real.cos θ : ℝ) : ℂ) - Complex.I * ((Real.sin θ : ℝ) : ℂ)) ^ 2 *
                      ((((1 + x ^ 2) / y₁ ^ 2 - 1 / y₂ ^ 2 : ℝ) : ℂ) - Complex.I * (((2 * x / (y₁ * y₂) : ℝ) : ℂ)))) *
                  (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
                  ((|y₁ * y₂| : ℝ) : ℂ) *
                  (-Complex.I * (a : ℂ)) ^ n *
                  (((y₂ * Real.sin θ : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ)) ^ n *
                  ((1 / 2 : ℂ) *
                    ((Real.pi * (a : ℝ) ^ 2 * ((y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2) : ℝ) : ℂ)
                        ^ (-((P.centralExponent + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                    Complex.Gamma ((P.centralExponent + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
               ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) := by sorry
