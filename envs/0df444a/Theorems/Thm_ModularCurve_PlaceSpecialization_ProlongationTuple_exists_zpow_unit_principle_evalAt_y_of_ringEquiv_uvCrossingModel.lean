-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_zpow_unit_principle_evalAt_y_of_ringEquiv_uvCrossingModel
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_zpow_unit_principle_evalAt_y_of_ringEquiv_uvCrossingModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/88354511-780f-5248-a7d0-89466573d236
-- title:
--   Unit principle at a supersingular node of X₀(Nq)
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an $N\ge 1$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red}:A\to k$, modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of the two Hecke maps $\bar\alpha,\bar\beta$ at level $N$ and $q$, a place specialisation $P$ of these data, and a prolongation tuple $R$ over $P$; assume $q\nmid N$, that $R$ is a model (the two divisor laws and the two cusp laws) and satisfies the order law at $\varphi^2$-fixed affine geometric places. Let $K\subset\overline{\mathbb{Q}}$ be a finite extension of $\mathbb{Q}$ and let $w$ be a place of $\mathrm{modularFunctionFieldC}\,k\,N$ lying in $\mathrm{ssPlaces}\,q\,N\,k$, i.e. rational, affine geometric ($j$ and $j_N$ being $w$-integral) and with $w$-value of the $j$-generator a supersingular invariant. Assume the value-integrality law for $R$ at $w$ (every element of $R.\mathrm{nodeIntegers}\,w$ has $A$-integral value at every place of $\mathrm{modularFunctionFieldBar}(Nq)$ reducing to $w$ under $P.\mathrm{reduceFst}$), that the node ring $R.\mathrm{nodeIntegersOver}\,K\,w$ (elements integral for both prolongations and for all places above $w$, whose expansions lie in $\mathrm{NodeLocalized.fieldOver}(Nq)\,K$) is local and Noetherian, and that every $g$ in it differs from some constant $R.\mathrm{nodeConst}\,K\,w\,o$, $o\in A\cap K$, by a non-unit. Let $\varpi\in A\cap K$ generate the kernel of $\mathrm{NodeLocalized.redRestrict}\,\mathrm{red}\,K$, in the sense that $d$ has zero reduction exactly when $\varpi\mid d$. Let $W$ be a complete discrete valuation domain, adically complete for its maximal ideal, $\pi\in W$ irreducible, and $\sigma$ a ring homomorphism from $W$ to the adic completion of the node ring at its maximal ideal with $\sigma\pi$ the image of $R.\mathrm{nodeConst}\,K\,w\,\varpi$. Let $E\ge 1$ and let $\iota$ be a ring isomorphism from that completion onto $\mathrm{UVCrossingModel}\,W\,(\pi^E)=W[[U,V]]/(UV-\pi^E)$ carrying $\sigma o$ to the constant $o$ for all $o\in W$, and reading the two branch orders: if the first residue of $f$ at $w$ is nonzero of order $n$ then $\iota(f)$ is a unit multiple of $V^n$ modulo $(\pi,U)$, and if the second residue of $f$ at $\mathrm{arithFrobC}\,q\,k\,N\cdot w$ is nonzero of order $n$ then $\iota(f)$ is a unit multiple of $U^n$ modulo $(\pi,V)$. Finally let $c=(x,y)$ be node coordinates of $R$ over $K$ at $w$ with $xy=(R.\mathrm{nodeConst}\,K\,w\,\varpi)^{E_0}u$ for some $E_0\in\mathbb{N}$ and some unit $u$ of the node ring. Then for every nonzero $f$ in $\mathrm{modularFunctionFieldBar}(Nq)$ whose order vanishes at every place $V'$ with $P.\mathrm{reduceFst}\,V'=w$, there are $m\in\mathbb{Z}$ and $c_1\in\overline{\mathbb{Q}}$, $c_1\ne 0$, such that for every such place $V'$ the value $V'.\mathrm{evalAt}(f)\,c_1^{-1}\,(V'.\mathrm{evalAt}\,y)^{-m}$ lies in $A$ and is a unit of $A$.
--
--   This is the unit principle for the node annulus: a function with neither zeros nor poles among the places of $X_0(Nq)$ above a supersingular place $w$ of $X_0(N)_k$ has, at all those places, value equal to a fixed nonzero constant times an integral power of the value of the node parameter $y$, up to units of $A$. It is used in the identification of the places above $w$ with the annulus of the local crossing model $W[[U,V]]/(UV-\pi^E)$, in [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulus_dom_iff_reduceFst_eq_and_param_eq_y_of_ringEquiv_uvCrossingModel`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulus_dom_iff_reduceFst_eq_and_param_eq_y_of_ringEquiv_uvCrossingModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_zpow_unit_principle_evalAt_y_of_ringEquiv_uvCrossingModel.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem
    ModularCurve.PlaceSpecialization.ProlongationTuple.exists_zpow_unit_principle_evalAt_y_of_ringEquiv_uvCrossingModel
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (hord : R.OrderLawFixed)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hvalA : R.ValueIntegralityLaw w)
    (hres : ∀ g : ↥(R.nodeIntegersOver K w),
      ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))
    (hσπ : σ π = algebraMap _ _ (R.nodeConst K w ϖ))
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (hres₁ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₁ w ⟨f, f.2.1⟩ ≠ 0 →
          w.ord (R.nodeResidue₁ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hres₂ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₂ w ⟨f, f.2.1⟩ ≠ 0 →
          (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (c : R.NodeCoordinates K w) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u) :
    ∀ f : ↥(modularFunctionFieldBar (N * q)), f ≠ 0 →
      (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w → V'.ord f = 0) →
      ∃ (m : ℤ) (c₁ : AlgebraicClosure ℚ), c₁ ≠ 0 ∧
        ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V' = w →
          ∃ h : V'.evalAt f * c₁⁻¹ * V'.evalAt (↑c.y : ↥(modularFunctionFieldBar (N * q))) ^ (-m) ∈ A,
            IsUnit (⟨_, h⟩ : A) := by sorry
