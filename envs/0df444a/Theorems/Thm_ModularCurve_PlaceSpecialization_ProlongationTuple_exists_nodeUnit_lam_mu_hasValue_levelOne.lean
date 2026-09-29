-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeUnit_lam_mu_hasValue_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_nodeUnit_lam_mu_hasValue_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/9e07822b-e6f7-5b5a-8c01-57a8176c4d41
-- title:
--   Node unit and normalising constants as values at level one
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb{Q}}$, $k$ an algebraically closed field of characteristic $q$ and $red : A \to k$ a ring homomorphism; let `data` consist of a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j^{(q)})$ of $q$-expansions, subject to the Kronecker congruence $\Phi \equiv (C X^{q} - X)(C X - X^{q})$ modulo $q$, and assume the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` from level $1$ to level $q$ over $\overline{\mathbb{Q}}$ are integral. Let $P$ be a place specialization at level $N = 1$ for these data, and work with places of `modularFunctionFieldC k 1`, the intermediate field of $k((t))$ generated over $k$ by `jqModC k` and `jqNModC k 1`. Assume: $W$ is a finite set of such places whose members are exactly the supersingular places `ssPlaces q 1 k`; $R$ is a prolongation tuple for $P$ satisfying the regularity law relative to $W$; $K$ assigns to each place an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$; for each $w \in W$, `coord w` is a system of node coordinates $x, y$ in the node integer ring `R.nodeIntegersOver (K w) w` over $K w$ at $w$ (so that the first node residue of $x$ vanishes while the second has order $1$ at the Frobenius translate $\varphi \cdot w$, where $\varphi =$ `arithFrobC q k 1`, and symmetrically the second node residue of $y$ vanishes while the first has order $1$ at $w$); $u\,w$ is an element of that same node integer ring which is a unit in it; `cusp` is a place outside $W$; and $\pi_w =$ `unifFst w`, $\pi'_w =$ `unifSnd w` are elements of `modularFunctionFieldC k 1` whose divisors are $[w] - [\mathrm{cusp}]$ and $[\varphi \cdot w] - [\mathrm{cusp}]$ respectively, for every $w \in W$. Then there exist three families $u_0, \lambda, \mu$ of elements of $k^{\times}$, indexed by all places, such that for every $w \in W$: the first node residue `R.nodeResidue₁ w` of $u\,w$ lies in the valuation subring of $w$ and reduces there to $u_0(w)$; the quotient of the first node residue of $y$ by $\pi_w$ lies in the valuation subring of $w$ and reduces to $\lambda(w)$; and the quotient of the second node residue `R.nodeResidue₂ w` of $x$ by $\pi'_w$ lies in the valuation subring of $\varphi \cdot w$ and reduces there to $\mu(w)$.
--
--   This supplies the three families of non-zero constants attached to the supersingular crossings in the level-one situation: the residue at $w$ of the unit occurring in the node equation, and the two constants comparing the node parameters with the chosen global uniformisers at $w$ and at its Frobenius translate. It is used in the construction of the annulus datum at level one, [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulusDatumQ_laws_levelOne`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_annulusDatumQ_laws_levelOne), in the analysis of the special fibre of $X_0(q)$ at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeUnit_lam_mu_hasValue_levelOne.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_nodeUnit_lam_mu_hasValue_levelOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k 1))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hRL : R.RegularityLaw W)
    (K : Place k (modularFunctionFieldC k 1) → IntermediateField ℚ (AlgebraicClosure ℚ))
    (coord : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), R.NodeCoordinates (K w) w)
    (u : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), ↥(R.nodeIntegersOver (K w) w))
    (hu : ∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W), IsUnit (u w hw))
    (cusp : Place k (modularFunctionFieldC k 1)) (hcusp : cusp ∉ W)
    (unifFst unifSnd : Place k (modularFunctionFieldC k 1) → ↥(modularFunctionFieldC k 1))
    (hunif : ∀ w ∈ W,
      (∀ v : Place k (modularFunctionFieldC k 1),
          ((Finsupp.single w (1 : ℤ) - Finsupp.single cusp 1 :
              Divisor k ↥(modularFunctionFieldC k 1)) v) = v.ord (unifFst w)) ∧
      (∀ v : Place k (modularFunctionFieldC k 1),
          ((Finsupp.single (arithFrobC q k 1 • w) (1 : ℤ) - Finsupp.single cusp 1 :
              Divisor k ↥(modularFunctionFieldC k 1)) v) = v.ord (unifSnd w))) :
    ∃ (u0 lam mu : Place k (modularFunctionFieldC k 1) → kˣ),
      (∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨(u w hw : ↥(modularFunctionFieldBar (1 * q))), (u w hw).2.1⟩) ((u0 w : kˣ) : k)) ∧
      (∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨((coord w hw).y : ↥(modularFunctionFieldBar (1 * q))), (coord w hw).y.2.1⟩
        / unifFst w) ((lam w : kˣ) : k)) ∧
      (∀ (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W),
      (arithFrobC q k 1 • w).HasValue
        (R.nodeResidue₂ w ⟨((coord w hw).x : ↥(modularFunctionFieldBar (1 * q))), (coord w hw).x.2.1⟩
          / unifSnd w) ((mu w : kˣ) : k)) := by sorry
