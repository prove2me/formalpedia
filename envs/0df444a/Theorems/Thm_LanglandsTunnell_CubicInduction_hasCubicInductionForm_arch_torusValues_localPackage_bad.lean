-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_hasCubicInductionForm_arch_torusValues_localPackage_bad
-- name    : LanglandsTunnell.CubicInduction.hasCubicInductionForm_arch_torusValues_localPackage_bad
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/93fc1221-372f-578d-9237-0928e54c91a2
-- title:
--   Cubic automorphic induction: existence of a cubic induction form
-- statement:
--   Setting. $K$ is a number field whose ring of integers carries an integral $\mathcal O_{\mathbb Q}$-algebra structure, and the hypothesis `_hdeg` says $[K:\mathbb Q]=3$. Further data: a complex-valued additive character $\psi$ of the adele ring of $\mathbb Q$, with `_hψ` asserting that $\psi$ is a global additive character, i.e. trivial on the principal adeles $\psi(\alpha)=1$ for $\alpha\in\mathbb Q$, continuous and non-trivial; a character $\mu$ of the idele group of $K$ with values in $\mathbb C^\times$, with `_hμ` asserting that $\mu$ is an admissible twist, i.e. trivial on the principal ideles $K^\times$, continuous and of absolute value $1$ everywhere.
--
--   Level and non-norm-type hypotheses. `_hlev` requires the local level `addCharLevel (psiLoc ψ v)` to vanish at every finite place $v$ of $\mathbb Q$ that is not a bad place for $(K,\mu)$, a bad place being one that either is ramified in $K$ (some prime $\mathfrak P$ of $\mathcal O_K$ over $v$ has $e(\mathfrak P/v)\neq 1$) or satisfies the predicate `IsTwistRamifiedAbove K μ v`; `hlev` requires the same vanishing at every finite place of $\mathbb Q$ without exception, and so is the stronger statement. The hypothesis `_hns` states that $\mu$ is not of norm type: there is no admissible twist $\eta$ of the ideles of $\mathbb Q$ such that for every prime $\mathfrak P$ of $\mathcal O_K$ at which $\mu$ is unramified, lying over a prime $p$ at which $\eta$ is unramified, one has $\mu(\varpi_{\mathfrak P})=\eta(\varpi_p)^{f(\mathfrak P/p)}$, where $\varpi$ denotes the uniformizer idele and $f$ the inertia degree.
--
--   Archimedean parameters of $\mu$. Functions $uR$, $aR$ assign to each real place $w$ of $K$ a complex number and an element of $\mathbb Z/2$, and $uC$, $kC$ assign to each complex place a complex number and an integer. The hypotheses $huR$, $huC$ say that these are archimedean parameters of $\mu$ in the sense of `IsArchCompAt`: for every unit $x$ of the completion at $w$, the archimedean local component of $\mu$ at $w$ equals $\|x\|^{\mathrm{mult}(w)\,u}\,(x/\|x\|)^{a}$, with $(u,a)=(uR\,w,(aR\,w).\mathrm{val})$ at real $w$ and $(u,a)=(uC\,w,kC\,w)$ at complex $w$.
--
--   The central character $\omega$. A character $\omega$ of the ideles of $\mathbb Q$ is given, and $h\omega$ is the conjunction of three clauses: $\omega$ is an admissible twist; at every finite place $p$ of $\mathbb Q$ which is not bad for $(K,\mu)$, $\omega$ is unramified and `eulerCoeff ℚ ω p` (that is $\omega(\varpi_p)$) equals `inducedE3 ℚ (inducedCoeff K μ) p`, the negative of the degree-$3$ coefficient of the induced Euler polynomial formed from the coefficients $\mu(\varpi_{\mathfrak P})$ at unramified $\mathfrak P$ (and $0$ elsewhere); and, for every choice of archimedean parameters $uR,aR,uC,kC$ of $\mu$ as above, at every real place $v$ of $\mathbb Q$ the character $\omega$ has archimedean component with exponent $\sum_{w\ \mathrm{real}} uR\,w+\sum_{w\ \mathrm{complex}}2\,uC\,w$ and integer $\sum_{w\ \mathrm{real}}(aR\,w).\mathrm{val}+\sum_{w\ \mathrm{complex}}(kC\,w+1)$, the sums being finite sums over the infinite places of $K$.
--
--   Archimedean splitting and measures. $E$ is a homomorphism from the units of the infinite adele ring of $\mathbb Q$ to the idele group, with $hE$ saying that the infinite part of $E(u)$ is $u$ and its finite part is $1$. A non-zero rational $a$ is given, together with a unit $a_\infty$ of the infinite adele ring whose underlying element is the image of $a$ ($haInf$). The additive character $\psi_\infty$ satisfies $\psi_\infty(x)=\mathrm{psiArch}(a\,x)$ ($hpsiInf$), and $h\psi\mathrm{inf}$ says that the restriction of $\psi$ to the infinite part of the adeles is $\psi_\infty$. The infinite adele ring and its unit group carry their Borel measurable structures; $\nu_{\mathrm{add}}$ is the measure $|a|^{1/2}$ times the transport of Lebesgue measure along the inverse of the identification of the infinite adele ring with the mixed space ($h\nu_{\mathrm{add}}$), and $\nu_{\mathrm{mul}}$ is a Haar measure on the units.
--
--   The archimedean Whittaker function. $W_{\mathrm{arch}}$ is a complex-valued function on $\mathrm{GL}_3$ of the infinite adele ring, and $hW_{\mathrm{arch}}$ is a conjunction of six groups of clauses: (i) $W_{\mathrm{arch}}\neq 0$; (ii) $W_{\mathrm{arch}}$ is $K$-finite, i.e. the right translates by the elements of `orth3` lie in the span of a finite set of functions; (iii) $W_{\mathrm{arch}}$ is continuous and of moderate decay, namely there is $t\in\mathbb N$ such that for each $N$ there is $C$ with $\|W_{\mathrm{arch}}(g_\infty)\|\le C/\big((\prod_w \mathrm{archRoot}_1\,\mathrm{archRoot}_2)^t(1+\mathrm{archRootSum})^N\big)$ for all adelic $g$, $g_\infty$ its archimedean component; (iv) $W_{\mathrm{arch}}$ transforms under the upper unipotent by $\psi_\infty(x+y)$; (v) $W_{\mathrm{arch}}(z\cdot g)=\omega(E z)W_{\mathrm{arch}}(g)$ for scalar $z$; (vi) a zeta-integral package: for every admissible twist $\sigma$ of the ideles of $\mathbb Q$, every $t\in\mathbb C$ and $e\in\mathbb Z$ such that $\sigma$ has archimedean component $(t,e)$ at every real place of $\mathbb Q$, and every $g_\infty$, there is an entire function $P$ with the four properties that (a) for some $\sigma_0$ the $\mathrm{GL}_3\times\mathrm{GL}_1$ integral `archZeta30` of $h\mapsto W_{\mathrm{arch}}(h\,g_\infty)$ against $\sigma\circ E$ converges for $\mathrm{Re}\,s>\sigma_0$ and equals $P(s)$ times the archimedean factor of the Hecke datum `heckeDatum K μ` with parameters $(uR+t,\;aR+e,\;uC+t,\;kC)$; (b) $P$ is of bounded exponential type in every vertical strip, $\|P(s)\|\le C\exp(A|\mathrm{Im}\,s|)$; (c) in every vertical strip and for every $N$ the product of $P$ with that archimedean factor decays faster than $|\mathrm{Im}\,s|^{-N}$ for $|\mathrm{Im}\,s|$ large; (d) for some $\sigma_1$ the dual integral `archZeta31` of `dualWhittakerFn3` of $h\mapsto W_{\mathrm{arch}}(h\,g_\infty)$ against $(\sigma\circ E)^{-1}$ at `weylPrime3 * transposeInv3 1` converges, and for $\mathrm{Re}(1-s)>\sigma_1$ one has $\mathrm{archZetaDual31}(1-s)$ equal to the product of the archimedean root number $\big(\prod_{w\ \mathrm{real}}\mathrm{signEpsilon}(aR\,w+e)\big)\big(\prod_{w\ \mathrm{complex}}i^{|kC\,w|}\big)\prod_{w}\mathrm{lambdaArch}\,K\,w$ (where $\mathrm{lambdaArch}$ is $1$ at real places and $i$ at complex ones), times $\omega(E a_\infty)\,\sigma(E a_\infty)^3$, times $|a|^{3(s-1/2)}$, times $P(s)$, times the dual archimedean factor of the same Hecke datum at $1-s$; and finally a non-vanishing clause: for some admissible twist $\sigma$ of $\mathbb Q$ and some $s$, $\mathrm{archZeta30}(\nu_{\mathrm{mul}},W_{\mathrm{arch}},\sigma\circ E,s,1)\neq 0$.
--
--   Conclusion. For every set $D$ of adelic $\mathrm{GL}_2$ points, every assignment $U$ of subgroups of adelic $\mathrm{GL}_2$ to ideals of $\mathcal O_{\mathbb Q}$, and every assignment $\mathrm{gen}$ of adelic $\mathrm{GL}_2$ points to finite places, there exists a cubic induction form $F$ of type `CubicInductionForm K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ` — a structure carrying a function `form` on $\mathrm{GL}_3$ of the adeles of $\mathbb Q$, its global Whittaker function and dual Whittaker function, local Whittaker functions `whittakerLoc v` on $\mathrm{GL}_3$ of the completions at the finite places, an archimedean Whittaker function `whittakerArch`, and a central character, subject to conditions including left invariance under $\mathrm{GL}_3(\mathbb Q)$, the central character law with an idele class character, cuspidality along the two maximal parabolics, the identification of `whittaker` with the Whittaker integral of `form` and the mirabolic Fourier expansion summing back to `form`, the $\psi$- and $\psi_v$-Whittaker laws globally and locally, factorizability of `whittaker` as `whittakerArch` times the product of the local factors over any finite set containing all bad places, induced-sphericality at the good places, invariance under `congruenceK1` of level `inducedLevelAt K μ v` at places unramified in $K$, local Whittaker multiplicity one, moderate growth, $K$-finiteness of `whittakerArch` and the moment and half-plane conditions — such that all of the following hold.
--
--   First, `F.form ≠ 0`, and for every finite place $v$ of $\mathbb Q$ not ramified in $K$ at which `addCharLevel (psiLoc ψ v) = 0` one has `F.whittakerLoc v 1 = 1` and `HasSphericalTorusValuesAt (inducedCoeff K μ) v (F.whittakerLoc v)`, i.e. the values of `F.whittakerLoc v` at the torus points `iotaTorusLocal v n` and at the two-row points `twoRowPointLocal v k₁ (k₂+1)` with $k_2+1\le k_1$ are given by the displayed expressions in the spherical torus values of the induced Satake data `inducedE1`, `inducedE2`, `inducedE3` of `inducedCoeff K μ`, weighted by powers of `cNormQ v`.
--
--   Second, `F.form`, `F.whittaker` and `F.dualWhittaker` are continuous. Third, both `F.whittaker` and `F.dualWhittaker` are gauge majorised in the sense of `IsGaugeMajorised3`. Fourth, `F.whittakerArch = Warch`. Fifth, `F.centralChar = ω`.
--
--   Sixth, at every bad place $v$ and for every open subgroup $U_v$ of $\mathrm{GL}_3$ of the completion at $v$, there is a finite set $B$ of functions such that every element of the cyclic subspace generated by `F.whittakerLoc v` which is right $U_v$-invariant lies in the complex span of $B$. Seventh, at every bad place $v$ the local character `localChar ω v` has absolute value $1$ on units, and `F.whittakerLoc v` transforms under central elements $t$ by the factor `localChar ω v t`. Eighth, at every bad place $v$ the function `F.whittakerLoc v` satisfies `HasWhittakerMultOne (psiLoc ψ v)`.
--
--   Ninth, at every bad place $v$ which is ramified in $K$ there are natural numbers $e$ and $N$ such that `localChar ω v` has conductor exponent $e$ in the sense of `HasConductorExponentAt` (trivial on the $e$-th higher units and on no smaller group), such that $N$ satisfies the explicit conductor bound: for every $M$, if each prime $w$ in the fibre over $v$ admits a conductor exponent $a_w\le M$ for `localChar μ w`, then $N$ is at most twice the sum of the finite sum over $w$ in the fibre of $f(w)\big(e(w)\,(2(48+e+M)+\mathrm{addCharLevel}(\psi_{K,w})+2)+M+\mathrm{addCharLevel}(\psi_{K,w})+1\big)$ and of $48+e+M$, where $f$ and $e$ denote inertia degree and ramification index and $\psi_{K,w}$ the standard local additive character; and such that `F.whittakerLoc v` is invariant under right translation by those elements $k$ of the local maximal compact subgroup all of whose entries of $k-1$ have valuation at most $\exp(-N)$.
--
--   Tenth, at every bad place $v$ which is not ramified in $K$ and at which `psiLoc ψ v` is the inverse of the standard local character `psiLocal ℚ v`, there is a function $W$ in the cyclic subspace generated by `F.whittakerLoc v` which is a `psiLoc ψ v`-Whittaker function, is non-zero, is invariant under right translation by `congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v)`, satisfies $W(1)=1$ and satisfies `HasSphericalTorusValuesAt (inducedCoeff K μ) v W`.
--
--   Eleventh, for every finite set $T$ of finite places of $\mathbb Q$: at every bad $v\in T$ there is an open subgroup $U_v$ of $\mathrm{GL}_3$ of the completion at $v$ leaving `F.whittakerLoc v` invariant under right translation, and at every bad $v\in T$, for every non-zero $W$ in the cyclic subspace generated by `F.whittakerLoc v`, the function `F.whittakerLoc v` itself lies in the cyclic subspace generated by $W$.
--
--   This is the export form of the automorphic induction $\mathrm{AI}_{K/\mathbb Q}(\mu)$ for a cubic field $K$ and a non-norm-type idele class character $\mu$, obtained through the converse theorem for $\mathrm{GL}_3$, packaged together with the local information at the bad places (admissibility of the local Whittaker cyclic space, the unitary central law, Whittaker multiplicity one, an explicit level bound, and the essential vector at the unramified bad places) needed downstream. It is used in the Rankin–Selberg step that produces an entire completed $L$-function matching the archimedean factor of the Hecke datum of $\mu$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_hasCubicInductionForm_arch_torusValues_localPackage_bad.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda
  MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.hasCubicInductionForm_arch_torusValues_localPackage_bad
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (_hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
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
    (a : ℚ) (ha : a ≠ 0) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (hψinf : ψ.compAddMonoidHom
        (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = psiInf)
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (hWarch :
      Warch ≠ 0 ∧ IsKFinite Warch ∧
      (Continuous Warch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖Warch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) ∧
      IsGL3PsiWhittakerFn psiInf Warch ∧
      (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        Warch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((ω (E z) : ℂˣ) : ℂ) * Warch g) ∧
      (∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
        ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
        ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
          (∃ σ₀ : ℝ, IsArchZeta30ConvergentAbove ν_mul (fun h => Warch (h * gInf)) (σ.comp E) 1 σ₀ ∧
            ∀ s : ℂ, σ₀ < s.re →
              archZeta30 ν_mul (fun h => Warch (h * gInf)) (σ.comp E) s 1 =
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s) ∧
          (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ‖P s‖ ≤ C * Real.exp (A * |s.im|)) ∧
          (∀ (σ₁ σ₂ : ℝ) (N : ℕ), ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
            |s.im| ^ N *
              ‖P s *
                (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                  (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s‖ ≤ C) ∧
          (∃ σ₁ : ℝ, IsArchZeta31ConvergentAbove ν_mul ν_add (dualWhittakerFn3 (fun h => Warch (h * gInf)))
              (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
            ∀ s : ℂ, σ₁ < (1 - s).re →
              archZetaDual31 ν_mul ν_add (fun h => Warch (h * gInf)) (σ.comp E) (1 - s) 1 =
                (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
                    fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
                  ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                      fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
                  ∏ w : InfinitePlace K, lambdaArch K w) *
                (((ω (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul Warch (σ.comp E) s 1 ≠ 0) :
    ∀ (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
      (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ),
      ∃ F : CubicInductionForm K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ,
        (F.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
          LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
            F.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (F.whittakerLoc v)) ∧
        Continuous F.form ∧ Continuous F.whittaker ∧ Continuous F.dualWhittaker ∧
        IsGaugeMajorised3 ℚ F.whittaker ∧ IsGaugeMajorised3 ℚ F.dualWhittaker ∧
        F.whittakerArch = Warch ∧
        F.centralChar = ω ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v →
          ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
            ∃ B : Finset (LocalGL3 v → ℂ), ∀ G ∈ gl3CyclicSubspace (F.whittakerLoc v),
              (∀ k ∈ Uv, ∀ g : LocalGL3 v, G (g * k) = G g) → G ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v →
          (∀ z : (v.adicCompletion ℚ)ˣ, ‖((localChar ω v z : ℂˣ) : ℂ)‖ = 1) ∧
          ∀ (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
            F.whittakerLoc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
              ((localChar ω v t : ℂˣ) : ℂ) * F.whittakerLoc v h) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v → HasWhittakerMultOne (psiLoc ψ v) (F.whittakerLoc v)) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v → IsRamifiedIn K v →
          ∃ (e N : ℕ), LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar ω v) e ∧
            (∀ M : ℕ, (∀ w ∈ primeFibre ℚ K v, ∃ aw : ℕ, aw ≤ M ∧
                LanglandsTunnell.TateLocal.HasConductorExponentAt K w (localChar μ w) aw) →
              (N : ℤ) ≤ 2 * ((∑ᶠ w ∈ primeFibre ℚ K v,
                  ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal : ℤ) *
                    ((Ideal.ramificationIdx' (w.under (𝓞 ℚ)).asIdeal w.asIdeal : ℤ) *
                        (2 * ((48 : ℤ) + e + M) + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 2) +
                      M + LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K w) + 1)) +
                ((48 : ℤ) + e + M))) ∧
            ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
              (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
                  (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(N : ℤ))) →
              ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v → ¬ IsRamifiedIn K v →
          psiLoc ψ v = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ →
          ∃ W ∈ gl3CyclicSubspace (F.whittakerLoc v), IsGL3PsiWhittakerFn (psiLoc ψ v) W ∧ W ≠ 0 ∧
            (∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, W (g * k) = W g) ∧
            W 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v W) ∧
        ∀ T : Finset (HeightOneSpectrum (𝓞 ℚ)),
          (∀ v ∈ T, IsBadPlace K μ v → ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
            ∀ k ∈ Uv, ∀ g : LocalGL3 v, F.whittakerLoc v (g * k) = F.whittakerLoc v g) ∧
          (∀ v ∈ T, IsBadPlace K μ v → ∀ W ∈ gl3CyclicSubspace (F.whittakerLoc v), W ≠ 0 →
            F.whittakerLoc v ∈ gl3CyclicSubspace W) := by sorry
