-- Prove2me | Theorems.Thm_ModularCurve_exists_chartData_of_lineResidues
-- name    : ModularCurve.exists_chartData_of_lineResidues
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/9717a58c-74d4-5b7c-bfeb-a5595fe0d86e
-- title:
--   Chart data from a unit family with polynomial residues
-- statement:
--   Let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $k$ is algebraically closed, and let $F$ be a field over $\overline{\mathbb Q}$ in which every nonzero element has a degree-zero divisor recording its orders at all places (`HasPrincipalDivisors`), all of whose places are rational (the structure map $\overline{\mathbb Q}\to$ residue field is surjective). Let $C$ be a component chart for $A$ on $F$ with residue field of functions the level-one modular function field $k(\bar\jmath)=$ `modularFunctionFieldC k 1`: thus $C$ provides a valuation subring `C.integers` of $F$, a surjective residue map onto that field with kernel the maximal ideal, a set `C.dom` of places of $F$, a finite set of nodes, a map `C.placeMap` on places, and the compatibility axioms of `ComponentChart`. Let $s_0,\dots,s_{r-1}\in$ `C.integers` have nonzero residues, and let $D\neq 0$, $R_0,\dots,R_{r-1}$ be polynomials over $k$ with $\overline{s_l}\cdot D(\bar\jmath)=R_l(\bar\jmath)$, where $\bar\jmath$ is the class `jBar k` of $j$. Assume: a place $c_0\in$ `C.dom` with `C.placeMap` $c_0$ the place at infinity of $k(\bar\jmath)$ (transported by `charLGeomPlaceEquiv` from `RationalFunctionField.placeInfty`), every $s_l$ lying in the valuation subring of each other place of `C.dom`; each place of `C.dom` reduces either to a point $x_0$ with $D(x_0)\neq 0$ or to infinity; and the cusp law: for every element of `C.integers` with nonzero residue and every divisor $E$ computing its orders, the push-forward under `C.placeMap` of the part of $E$ supported on places of `C.dom` over infinity has value at infinity equal to the order of the residue there. Assume further the line algebra of $(D,R)$: index functions $c,i:k\to \mathrm{Fin}\,r$ and a finite set $H$ such that at every reduced affine point $x_0$ one has $R_{c(x_0)}(x_0)\neq 0$, the polynomial $R_{i(x_0)}R_{c(x_0)}(x_0)-R_{c(x_0)}R_{i(x_0)}(x_0)$ has $x_0$ as a simple root, some $l\in H$ has $R_l(x_0)\neq 0$, and distinct reduced affine points are separated by a nonvanishing $2\times2$ minor of evaluations; at infinity, indices $c_\infty,i_\infty$ with $\deg R_{c_\infty}$ maximal among the $R_l$ and $\geq\deg D$, $c_\infty\in H$, the pole bound $\operatorname{ord}_{c_0}(s_l)\geq-(\deg R_{c_\infty}-\deg D)$ for all $l$, the polynomial $R_{i_\infty}-\bigl(\mathrm{coeff}_{\deg R_{c_\infty}}R_{i_\infty}/\mathrm{lc}\,R_{c_\infty}\bigr)R_{c_\infty}$ nonzero of degree $\deg R_{c_\infty}-1$, and separation of each reduced affine point from infinity by a minor formed from evaluations against these top-coefficient ratios. The conclusion asserts the existence of index functions $c_Q,i_Q$ on the places of $k(\bar\jmath)$ such that, for all $P\in$ `C.dom`: $P$ and `C.placeMap` $P$ are rational; the residue of $s_{c_Q(\mathrm{placeMap}\,P)}$ is nonzero; all ratios $s_j\,s_{c_Q(\mathrm{placeMap}\,P)}^{-1}$ lie in `C.integers` and in the valuation subring of $P$; the residue of $s_{i_Q(\mathrm{placeMap}\,P)}s_{c_Q(\mathrm{placeMap}\,P)}^{-1}$, minus the constant given by its value at `C.placeMap` $P$, has order exactly $1$ there; any two places of `C.dom` with distinct images are separated by a nonvanishing $2\times2$ minor of the values of such ratios; and for every absolute value $\mu$ on $\overline{\mathbb Q}$ with $A=\{\mu\leq1\}$ there is $l\in H$ with $\mu\bigl(P.\mathrm{evalAt}(s_l\,s_{c_Q(\mathrm{placeMap}\,P)}^{-1})\bigr)=1$.
--
--   This is the generic passage from a family of chart units whose residues are read as polynomials in $j$ to the chart data (pivot and immersion indices, regularity of ratios, simple-order immersion, separation of distinct reduced points, and units of absolute value one) required of the charts of the multiplicative covering of the modular curve. It is applied to the individual charts by [`ModularCurve.MultCovering.infChart_chartData_goodFamily`](thm.html#ModularCurve.MultCovering.infChart_chartData_goodFamily) and the two `zeroChart_chartData_goodFamilyZero_…` lemmas, each of which then has only polynomial algebra over $k$ to verify.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_chartData_of_lineResidues.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

open Classical in

theorem ModularCurve.exists_chartData_of_lineResidues
    {A : ValuationSubring (AlgebraicClosure ℚ)} [DecidableEq (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] [HasPrincipalDivisors (AlgebraicClosure ℚ) F]
    (hFrat : ∀ P : Place (AlgebraicClosure ℚ) F, P.IsRational)
    (C : ComponentChart A F ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
    {r : ℕ} (s : Fin r → F) (hint : ∀ l, s l ∈ C.integers) (hunit : ∀ l, C.residue ⟨s l, hint l⟩ ≠ 0)

    (D : Polynomial (IsLocalRing.ResidueField ↥A)) (R : Fin r → Polynomial (IsLocalRing.ResidueField ↥A)) (hD : D ≠ 0)
    (hR : ∀ l, (C.residue ⟨s l, hint l⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) D
      = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R l))

    (c₀ : Place (AlgebraicClosure ℚ) F) (hc₀ : c₀ ∈ C.dom)
    (hc₀inf : C.placeMap c₀ = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)))
    (hreg₀ : ∀ P ∈ C.dom, P ≠ c₀ → ∀ l, s l ∈ P.toValuationSubring)

    (hdom : ∀ P ∈ C.dom, (∃ x₀ : IsLocalRing.ResidueField ↥A, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ ∧ D.eval x₀ ≠ 0) ∨
      C.placeMap P = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)))

    (hcusp : ∀ (f : F) (hf : f ∈ C.integers), C.residue ⟨f, hf⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) F, (∀ W, E W = W.ord f) →
        Finsupp.mapDomain C.placeMap
            (E.filter (fun W => W ∈ C.dom ∧ C.placeMap W = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))))
            (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)))
          = (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord (C.residue ⟨f, hf⟩))

    (c i : IsLocalRing.ResidueField ↥A → Fin r) (H : Finset (Fin r))
    (hcx : ∀ P ∈ C.dom, ∀ x₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ → (R (c x₀)).eval x₀ ≠ 0)
    (hix : ∀ P ∈ C.dom, ∀ x₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ →
      (R (i x₀) * Polynomial.C ((R (c x₀)).eval x₀) - R (c x₀) * Polynomial.C ((R (i x₀)).eval x₀)).rootMultiplicity x₀ = 1)
    (hsepx : ∀ P ∈ C.dom, ∀ Q ∈ C.dom, ∀ x₀ y₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ → C.placeMap Q = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) y₀ → x₀ ≠ y₀ →
      ∃ a b, (R a).eval x₀ * (R b).eval y₀ ≠ (R b).eval x₀ * (R a).eval y₀)
    (hHx : ∀ P ∈ C.dom, ∀ x₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ → ∃ l ∈ H, (R l).eval x₀ ≠ 0)

    (cInf iInf : Fin r) (hcInf : ∀ l, (R l).natDegree ≤ (R cInf).natDegree) (hcInfD : D.natDegree ≤ (R cInf).natDegree) (hcInfH : cInf ∈ H)
    (hpole : ∀ l, -(((R cInf).natDegree - D.natDegree : ℕ) : ℤ) ≤ c₀.ord (s l))
    (hiInf : (R iInf - Polynomial.C ((R iInf).coeff (R cInf).natDegree / (R cInf).leadingCoeff) * R cInf).natDegree + 1
      = (R cInf).natDegree)
    (hiInf0 : R iInf - Polynomial.C ((R iInf).coeff (R cInf).natDegree / (R cInf).leadingCoeff) * R cInf ≠ 0)
    (hsepInf : ∀ P ∈ C.dom, ∀ x₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ →
      ∃ a b, (R a).eval x₀ * ((R b).coeff (R cInf).natDegree / (R cInf).leadingCoeff)
        ≠ (R b).eval x₀ * ((R a).coeff (R cInf).natDegree / (R cInf).leadingCoeff)) :
    ∃ (cQ iQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) → Fin r),
      (∀ P ∈ C.dom, P.IsRational ∧ (C.placeMap P).IsRational) ∧
      (∀ P ∈ C.dom, C.residue ⟨s (cQ (C.placeMap P)), hint _⟩ ≠ 0) ∧
      (∀ P ∈ C.dom, ∀ j, s j * (s (cQ (C.placeMap P)))⁻¹ ∈ C.integers) ∧
      (∀ P ∈ C.dom, ∀ j, s j * (s (cQ (C.placeMap P)))⁻¹ ∈ P.toValuationSubring) ∧
      (∀ P ∈ C.dom, ∀ hmem : s (iQ (C.placeMap P)) * (s (cQ (C.placeMap P)))⁻¹ ∈ C.integers,
        (C.placeMap P).ord (C.residue ⟨_, hmem⟩
          - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) ((C.placeMap P).evalAt (C.residue ⟨_, hmem⟩))) = 1) ∧
      (∀ P ∈ C.dom, ∀ Q ∈ C.dom, C.placeMap P ≠ C.placeMap Q →
        ∀ (hmP : ∀ j, s j * (s (cQ (C.placeMap P)))⁻¹ ∈ C.integers)
          (hmQ : ∀ j, s j * (s (cQ (C.placeMap Q)))⁻¹ ∈ C.integers),
        ∃ i' j', (C.placeMap P).evalAt (C.residue ⟨_, hmP i'⟩) * (C.placeMap Q).evalAt (C.residue ⟨_, hmQ j'⟩)
          ≠ (C.placeMap P).evalAt (C.residue ⟨_, hmP j'⟩) * (C.placeMap Q).evalAt (C.residue ⟨_, hmQ i'⟩)) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P ∈ C.dom, ∃ l ∈ H, μ (P.evalAt (s l * (s (cQ (C.placeMap P)))⁻¹)) = 1) := by sorry
