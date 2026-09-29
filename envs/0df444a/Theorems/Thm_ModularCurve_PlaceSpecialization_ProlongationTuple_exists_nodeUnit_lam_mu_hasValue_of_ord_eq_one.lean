-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeUnit_lam_mu_hasValue_of_ord_eq_one
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_nodeUnit_lam_mu_hasValue_of_ord_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/390d9530-61aa-51de-b451-b13ec4d6dab6
-- title:
--   Node units and uniformiser ratios take values in k^×
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an integer $N\ge 1$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$, together with modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr` and the integrality hypotheses $h\alpha$, $h\beta$ on the Hecke operators $\bar\alpha$, $\bar\beta$ at level $N$ and prime $q$ over $\overline{\mathbb Q}$. Let $P$ be a place specialisation of these data, $W$ a finite set of places of the level-$N$ fibre field `modularFunctionFieldC k N` all lying in `ssPlaces q N k`, and $R$ a prolongation tuple for $P$ satisfying `RegularityLaw W`. Assume given, for each place $w$, an intermediate field $K_w$ of $\overline{\mathbb Q}/\mathbb Q$, and for each $w\in W$: node coordinates $(x_w,y_w)$ over $K_w$ at $w$ — so $x_w,y_w$ lie in the subring `R.nodeIntegersOver (K w) w` of `modularFunctionFieldBar (N*q)` of node integers at $w$ whose Laurent expansions have coefficients in the field over $K_w$, with `nodeResidue₁` of $x_w$ zero and $\operatorname{ord}$ of `nodeResidue₂` of $x_w$ equal to $1$ at the Frobenius translate $\varphi w :=$ `arithFrobC q k N • w`, and `nodeResidue₂` of $y_w$ zero and $\operatorname{ord}_w$ of `nodeResidue₁` of $y_w$ equal to $1$ — an element $u_w$ of the same node ring which is a unit there, and elements $\pi_w,\pi'_w$ of `modularFunctionFieldC k N` with $\operatorname{ord}_w(\pi_w)=1$ and $\operatorname{ord}_{\varphi w}(\pi'_w)=1$. Then there exist three families $u_0,\lambda,\mu$ of elements of $k^\times$, indexed by all places, such that for every $w\in W$ the function `nodeResidue₁ w` of $u_w$ has value $u_0(w)$ at $w$, the function (`nodeResidue₁ w` of $y_w$)$/\pi_w$ has value $\lambda(w)$ at $w$, and (`nodeResidue₂ w` of $x_w$)$/\pi'_w$ has value $\mu(w)$ at $\varphi w$; here 'has value $a$ at $v$' means that the function lies in the valuation subring of $v$ and its residue is the image of $a$ in the residue field of $v$.
--
--   This is the step that converts the two residues of the node data at a supersingular crossing $(w,\varphi w)$ into honest non-zero constants of $k$: the residue of a node unit, and the leading coefficients of the two local coordinates measured against given local uniformisers. It is used in the construction of the annulus datum at level $N$, via `exists_annulusDatumLevel_laws`; compared with the level-one form of the statement, the global condition $\operatorname{div}(\pi_w)=[w]-[\bar\infty]$ is replaced by the purely local requirement that $\pi_w$, $\pi'_w$ have order one at $w$, $\varphi w$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeUnit_lam_mu_hasValue_of_ord_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_nodeUnit_lam_mu_hasValue_of_ord_eq_one
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hRL : R.RegularityLaw W)
    (K : Place k (modularFunctionFieldC k N) → IntermediateField ℚ (AlgebraicClosure ℚ))
    (coord : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), R.NodeCoordinates (K w) w)
    (u : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), ↥(R.nodeIntegersOver (K w) w))
    (hu : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), IsUnit (u w hw))
    (unifFst unifSnd : Place k (modularFunctionFieldC k N) → ↥(modularFunctionFieldC k N))
    (hunifFst : ∀ w ∈ W, w.ord (unifFst w) = 1)
    (hunifSnd : ∀ w ∈ W, (arithFrobC q k N • w).ord (unifSnd w) = 1) :
    ∃ (u0 lam mu : Place k (modularFunctionFieldC k N) → kˣ),
      (∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨(u w hw : ↥(modularFunctionFieldBar (N * q))), (u w hw).2.1⟩) ((u0 w : kˣ) : k)) ∧
      (∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      w.HasValue (R.nodeResidue₁ w ⟨((coord w hw).y : ↥(modularFunctionFieldBar (N * q))), (coord w hw).y.2.1⟩
        / unifFst w) ((lam w : kˣ) : k)) ∧
      (∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      (arithFrobC q k N • w).HasValue
        (R.nodeResidue₂ w ⟨((coord w hw).x : ↥(modularFunctionFieldBar (N * q))), (coord w hw).x.2.1⟩
          / unifSnd w) ((mu w : kˣ) : k)) := by sorry
