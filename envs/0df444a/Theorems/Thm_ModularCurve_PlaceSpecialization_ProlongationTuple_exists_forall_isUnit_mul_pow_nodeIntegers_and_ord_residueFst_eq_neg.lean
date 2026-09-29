-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/0582887e-0ace-5384-b5e7-9cd4285cf1f7
-- title:
--   Seed function for the vertical cycle at supersingular nodes
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive integer $N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} \colon A \to k$; fix modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr` (the reduction mod $q$ of $\Phi$ is $(C X^q - X)(C X - X^q)$), integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings of $\overline{\mathbb{Q}}$-Laurent modular function fields from level $N$ to level $Nq$, a place specialisation $P$ of these data, and a prolongation tuple $R$ over $P$. Assume $q \nmid N$, that $R$ is a model (the two divisor laws and the two cusp laws), and let $W$ be a finite set of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places (rational, affine in $j$ and $j_N$, with supersingular $j$-value); assume the regularity law and the node-value law at $W$, and the order law at Frobenius-fixed affine places. Suppose given, for each place $w$, an element $y_w$ of the level-$Nq$ field and an exponent $n_w \in \mathbb{N}$ such that, for $w \in W$: $y_w$ lies in the node ring at $w$, i.e. in the integers of $R_1$ and of $R_2$ and in every valuation subring $V$ of the level-$Nq$ field over $\overline{\mathbb{Q}}$ with $P.\mathrm{reduceFst}\,V = w$; the $R_1$-residue of $y_w$ is nonzero; $\mathrm{ord}_V(y_w) = 0$ for every such $V$; the element `R.residue₁` of $y_w$ has order $1$ at $w$; and for all $w, w' \in W$ the element $y_w^{n_w}(y_{w'}^{n_{w'}})^{-1}$ lies in the integers of $R_2$ with nonzero $R_2$-residue. Then there is a nonzero $f$ in the level-$Nq$ field lying in the integers of $R_1$, with nonzero $R_1$-residue, such that for every $w \in W$ the element `R.residue₁` of $f$ has order $-n_w$ at $w$, the product $f\,y_w^{n_w}$ lies in the node ring at $w$ and is a unit there, and $\mathrm{ord}_V(f) = 0$ for every place $V$ of the level-$Nq$ field over $\overline{\mathbb{Q}}$ with $P.\mathrm{reduceFst}\,V = w$.
--
--   This is the nodes-only form of the semilocal principality of the vertical cycle supported on the second copy of the reduction of $X_0(Nq)$ at the supersingular points: the function $f$ realises, simultaneously at all supersingular nodes, poles of exact orders $n_w$ on the first component while remaining a unit in each node ring after multiplication by $y_w^{n_w}$. It feeds the subsequent statement combining these node conditions with the order data at the remaining places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W) (hO : R.OrderLawFixed)
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
        (∀ (w) (_ : w ∈ W), w.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) = -((n w : ℕ) : ℤ))) ∧
      (∀ (w) (hw : w ∈ W), ∃ h : f * y w ^ n w ∈ R.nodeIntegers w,
        IsUnit (⟨f * y w ^ n w, h⟩ : ↥(R.nodeIntegers w))) ∧
      (∀ w ∈ W, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        P.reduceFst V = w → V.ord f = 0) := by sorry
