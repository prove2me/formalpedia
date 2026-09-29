-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeIntegersOver_isLocalRing_exists_isMaximal_of_regularityLaw
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.nodeIntegersOver_isLocalRing_exists_isMaximal_of_regularityLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/852f7eed-7909-5303-9db1-bc79b0004aab
-- title:
--   Node ring at a supersingular place is a localisation
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a nonzero level $N$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Let `data` be a `ModularPolynomialData q`, i.e. a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, let `hKr` assert the Kronecker congruence that the bivariate reduction of $\Phi$ modulo $q$ equals $(X^q - Y)(X - Y^q)$, and let `hα`, `hβ` assert that the ring homomorphisms $\overline{\alpha}$, $\overline{\beta}$ attached to the Hecke correspondence at $q$ and level $N$ are integral. Given a `PlaceSpecialization` $P$ for these data and a `ProlongationTuple` $R$ over $P$, with $k$ algebraically closed, assume $q \nmid N$, that $R$ satisfies `OrderLawFixed` (the order law at Frobenius-square-fixed affine geometric places), that $W$ is a finite set of places of `modularFunctionFieldC k N` all lying in `ssPlaces q N k`, that $R$ satisfies `RegularityLaw W`, that $K \subseteq \overline{\mathbb{Q}}$ is a number field, and that $w \in W$. Then the subring $R.\mathrm{nodeIntegersOver}\,K\,w$ of `modularFunctionFieldBar (N * q)`, consisting of those $f$ lying in `R.nodeIntegers w` whose Laurent series lies in `NodeLocalized.fieldOver (N * q) K`, is a local ring and is Noetherian, and there is a maximal ideal $\mathfrak{m}$ of `jIntegralClosure (N * q) A K` — the ring of elements of `fieldOver (N * q) K` integral over `jRing A K` — such that an element $g$ of `modularFunctionFieldBar (N * q)` belongs to $R.\mathrm{nodeIntegersOver}\,K\,w$ if and only if there exist $r, s$ in that integral closure with $s \notin \mathfrak{m}$ and $g\,s = r$ as Laurent series; that is, the node ring is the localisation of the integral closure at $\mathfrak{m}$.
--
--   This identifies the ring of $K$-rational modular functions of level $Nq$ that are integral for both prolongations and regular above a supersingular place $w$ with a localisation of the normalisation of the $j$-line at level $Nq$, so that $w$ corresponds to a maximal ideal of that normalisation. It is used in the study of the node residue under specialisation and in the comparison of the completed local ring at a supersingular point with the local ring of a crossing model on $X_0(Nq)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeIntegersOver_isLocalRing_exists_isMaximal_of_regularityLaw.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem
    ModularCurve.PlaceSpecialization.ProlongationTuple.nodeIntegersOver_isLocalRing_exists_isMaximal_of_regularityLaw
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data} {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) :
    IsLocalRing ↥(R.nodeIntegersOver K w) ∧ IsNoetherianRing ↥(R.nodeIntegersOver K w) ∧
    ∃ 𝔪 : Ideal ↥(jIntegralClosure (N * q) A K), 𝔪.IsMaximal ∧
      ∀ g : ↥(modularFunctionFieldBar (N * q)), g ∈ R.nodeIntegersOver K w ↔
        ∃ r s : ↥(jIntegralClosure (N * q) A K), s ∉ 𝔪 ∧
          (g : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ))
            = (r : LaurentSeries (AlgebraicClosure ℚ)) := by sorry
