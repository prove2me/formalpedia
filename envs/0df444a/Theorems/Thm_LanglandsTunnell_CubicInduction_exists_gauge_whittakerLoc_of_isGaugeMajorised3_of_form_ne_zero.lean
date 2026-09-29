-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_gauge_whittakerLoc_of_isGaugeMajorised3_of_form_ne_zero
-- name    : LanglandsTunnell.CubicInduction.exists_gauge_whittakerLoc_of_isGaugeMajorised3_of_form_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/0e5ddb32-b283-5265-bb9d-1f3e8b93253a
-- title:
--   Gauge majorant descends to the local Whittaker function at v
-- statement:
--   Let $K$ be a number field equipped with an integral $\mathcal O_{\mathbb Q}$-algebra structure on $\mathcal O_K$, let `pins : CarrierPins ℚ` be a bundle of carrier data over $\mathbb Q$ (a measurable space and measure on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$, a subset $D$ of it, a subgroup $Z$ of the ideles, a family of subgroups indexed by ideals of $\mathcal O_{\mathbb Q}$, a choice of adelic matrix for each finite place, and a measurable space and measure on the adeles), let $\psi$ be an additive character of $\mathbb A_{\mathbb Q}$ with values in $\mathbb C$, and let $\mu$ be a homomorphism from the ideles of $K$ to $\mathbb C^\times$. Let $F$ be a cubic induction datum of type `CubicInductionForm K pins ψ μ`: it carries a function `F.form` on $\mathrm{GL}_3(\mathbb A_{\mathbb Q})$, a global Whittaker function `F.whittaker`, local Whittaker functions `F.whittakerLoc v` on $\mathrm{GL}_3(\mathbb Q_v)$ for each finite place $v$, an archimedean factor, a central character and a dual Whittaker function, subject to the axioms of that structure (automorphy under $\mathrm{GL}_3(\mathbb Q)$, the central character law with an idele class character, cuspidality along the two maximal parabolics, the $\psi$-Whittaker law and the mirabolic expansion of `F.form`, the Euler factorisation of `F.whittaker` over any finite set containing the bad places of $\mu$ and the places where the component is not integral, sphericity and level invariance away from bad places, local multiplicity one, moderate growth, $K$-finiteness and the remaining analytic axioms), summarised here. Assume `F.form ≠ 0`; assume `IsGaugeMajorised3 ℚ F.whittaker`, that is, there are $t \in \mathbb N$, a finite set $T$ of finite places and $B \in \mathbb R$ such that for every $N$ there is $C$ with `F.whittaker g = 0` unless `InRootLevel ℚ T B g` holds, and $\|{}$`F.whittaker g`$\|\le C/(\,$`rootSizeProd ℚ g`$^t(1+$`archRootSum ℚ g`$)^N)$ when it does. Let $S'$ be a finite set of finite places such that every place outside $S'$ is neither ramified in $K$ nor twist-ramified above for $\mu$ (i.e. `IsBadPlace K μ` fails there), and fix a finite place $v$. Then there exist $B \in \mathbb R$, $t \in \mathbb N$ and $C \in \mathbb R$ such that for every $h \in \mathrm{GL}_3(\mathbb Q_v)$, writing $\rho_1(h) = \lVert\det h\rVert\, r(h)/m(h)^2$ and $\rho_2(h) = m(h)/r(h)^2$, where $r(h)$ is the maximum of the norms of the three entries of the last row and $m(h)$ the maximum of the norms of the three $2\times 2$ minors `bottomMinor h 0 1`, `bottomMinor h 0 2`, `bottomMinor h 1 2`: one has `F.whittakerLoc v h = 0` unless both $\rho_1(h)\le B$ and $\rho_2(h)\le B$, and $\|$`F.whittakerLoc v h`$\| \le C/(\rho_1(h)\rho_2(h))^t$ whenever both $\rho_1(h)\le B$ and $\rho_2(h)\le B$. No positivity is asserted of $B$ or $C$, and the exponent $t$ is a single natural number (there is no archimedean parameter $N$ in the local bound).
--
--   This is the local counterpart, at a single finite place, of the gauge majorant for Whittaker functions on $\mathrm{GL}_3$: the support condition and the polynomial bound in the two root sizes $\rho_1,\rho_2$ of an Iwasawa decomposition are transferred from the global Whittaker function of a cubic induction datum to each of its local factors, using the Euler factorisation and the non-vanishing of the form. It is used in the construction of test vectors invariant under a congruence subgroup and in the convergence and analytic continuation statements for the Rankin–Selberg integrals attached to the cubic induction datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_gauge_whittakerLoc_of_isGaugeMajorised3_of_form_ne_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_gauge_whittakerLoc_of_isGaugeMajorised3_of_form_ne_zero
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (F : CubicInductionForm K pins ψ μ) (hF0 : F.form ≠ 0) (hFg : IsGaugeMajorised3 ℚ F.whittaker)
    (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hgood : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S' → ¬ IsBadPlace K μ p)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) →
        F.whittakerLoc v h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖F.whittakerLoc v h‖ ≤
          C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) := by sorry
