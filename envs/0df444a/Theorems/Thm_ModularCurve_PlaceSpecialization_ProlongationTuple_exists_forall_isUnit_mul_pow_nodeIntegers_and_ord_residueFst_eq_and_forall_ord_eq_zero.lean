-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_and_forall_ord_eq_zero
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_and_forall_ord_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/c524c70c-a49d-587c-b2d4-747a7527f5cd
-- title:
--   Function realising prescribed node units and residue orders -n_w
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an integer $N\ne 0$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red}\colon A\to k$, modular polynomial data `data` for $q$ (a monic $\Phi\in\mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions of $j$) together with a proof `hKr` that its reduction mod $q$ is $(\,^{C}\!X^{q}-X)(\,^{C}\!X-X^{q})$, a place specialisation $P$ of level $N$ at $A$ over $\mathrm{red}$ with respect to the integrality data $h\alpha,h\beta$ for the two degeneracy maps, and a prolongation tuple $R$ over $P$, with $q\nmid N$. Assume $R$ is a model (the two divisor laws and the two cusp laws hold), and let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,N$ consisting exactly of the supersingular places (rational, affine geometric, with $j$-value in the supersingular set for $q$); assume the regularity law and the node-value law at $W$, and the order law at $\varphi^{2}$-fixed affine places, where $\varphi=$ `frobOnPlacesGeomLevel`. Let $Z$ be a finite set consisting exactly of the places $v$ with $\varphi(\varphi(v))=v$. Let $y$ assign to each place an element of $\mathrm{modularFunctionFieldBar}(Nq)$ and $n$ assign a natural number, such that for all $w\in W$: $y_w$ lies in the node ring at $w$ (integral for both prolongations $R_1,R_2$ and in the valuation ring of every place $V$ of $\overline{\mathbb{Q}}$-level $Nq$ with $P.\mathrm{reduceFst}\,V=w$); $y_w$ is $R_1$-integral with nonzero first residue; $V.\mathrm{ord}(y_w)=0$ for every such $V$ above $w$; the first residue of $y_w$ has order $1$ at $w$; and for all $w,w'\in W$ the element $y_w^{\,n_w}(y_{w'}^{\,n_{w'}})^{-1}$ is $R_2$-integral with nonzero second residue. Then there is a nonzero $f\in\mathrm{modularFunctionFieldBar}(Nq)$ which is $R_1$-integral with nonzero first residue $\bar f_1$, such that $\mathrm{ord}_w(\bar f_1)=-n_w$ for every $w\in W$; for every divisor $G$ with $G(V)=V.\mathrm{ord}(f)$ at all $V$ and every place $v\notin W$, the pushforward along $P.\mathrm{reduceFst}$ of the strict-first part $P.\mathrm{fstDiv}\,G$ of $G$ takes the value $\mathrm{ord}_v(\bar f_1)$ at $v$; for every $w\in W$ the product $f\,y_w^{\,n_w}$ lies in the node ring at $w$ and is a unit there; and $V.\mathrm{ord}(f)=0$ for every $z\in Z$ and every $V$ with $P.\mathrm{reduceFst}\,V=z$.
--
--   This is the analytic form of the width computation for the two-copy special fibre of $X_0(Nq)$: the function $f$ realises the primitive vertical cycle, being a unit at each supersingular node after multiplication by $y_w^{\,n_w}$, having first-copy residue orders $-n_w$, and being order-zero above all $\varphi^{2}$-fixed places. It strengthens the corresponding statement without the divisor clause and the order-zero clause by recording, off $W$, that the pushforward of the strict-first part of $\mathrm{div}(f)$ computes the divisor of $\bar f_1$, and it is used in the construction of a good divisor with first-copy residue orders $-\,\mathrm{lcm}/\mathrm{width}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_and_forall_ord_eq_zero.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_and_forall_ord_eq_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W) (hO : R.OrderLawFixed)
    (Z : Finset (Place k (modularFunctionFieldC k N)))
    (hZ : ∀ v : Place k (modularFunctionFieldC k N),
      v ∈ Z ↔ frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v)
    (y : Place k (modularFunctionFieldC k N) → ↥(modularFunctionFieldBar (N * q)))
    (n : Place k (modularFunctionFieldC k N) → ℕ)
    (hyS : ∀ w ∈ W, y w ∈ R.nodeIntegers w)
    (hy₁ : ∀ w ∈ W, ∃ h : y w ∈ R.R₁.integers, R.R₁.residue ⟨y w, h⟩ ≠ 0)
    (hyV : ∀ w ∈ W, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = w → V.ord (y w) = 0)
    (hy_ord1 : ∀ (w) (_ : w ∈ W) (h : y w ∈ R.R₁.integers),
      w.ord (R.residue₁ ⟨y w, h⟩ : ↥(modularFunctionFieldC k N)) = 1)
    (hvert : ∀ w ∈ W, ∀ w' ∈ W,
      ∃ h : y w ^ n w * (y w' ^ n w')⁻¹ ∈ R.R₂.integers, R.R₂.residue ⟨y w ^ n w * (y w' ^ n w')⁻¹, h⟩ ≠ 0) :
    ∃ f : ↥(modularFunctionFieldBar (N * q)), f ≠ 0 ∧
      (∃ h₁ : f ∈ R.R₁.integers, R.R₁.residue ⟨f, h₁⟩ ≠ 0 ∧
        (∀ (w) (_ : w ∈ W), w.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) = -((n w : ℕ) : ℤ)) ∧
        (∀ G : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          (∀ V, G V = V.ord f) →
          ∀ v : Place k (modularFunctionFieldC k N), v ∉ W →
            Finsupp.mapDomain P.reduceFst (P.fstDiv G) v
              = v.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)))) ∧
      (∀ (w) (hw : w ∈ W), ∃ h : f * y w ^ n w ∈ R.nodeIntegers w,
        IsUnit (⟨f * y w ^ n w, h⟩ : ↥(R.nodeIntegers w))) ∧
      (∀ z ∈ Z, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        P.reduceFst V = z → V.ord f = 0) := by sorry
