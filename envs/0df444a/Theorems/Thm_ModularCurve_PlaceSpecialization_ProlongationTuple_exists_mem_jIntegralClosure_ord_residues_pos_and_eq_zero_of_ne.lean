-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/1baef0b8-28e5-5237-a5bd-7dc64d2e95c9
-- title:
--   Separating supersingular places by functions integral over the j-ring
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a natural number $N \neq 0$, and a field $k$ of characteristic $q$ together with a ring homomorphism $\mathrm{red} : A \to k$; fix moreover modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions) satisfying the Kronecker congruence, namely that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$, hypotheses $h\alpha$, $h\beta$ asserting that the Hecke $\bar\alpha$- and $\bar\beta$-homomorphisms at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral, a place specialisation $P$ for these data, and a prolongation tuple $R$ over $P$ (a residue-field map $\bar{\mathrm{red}}$ lifting $\mathrm{red}$, an embedding $\iota$ of modular function fields, and two regular prolongations $R_1$, $R_2$ of $\overline{\mathcal{F}}(Nq)$, the second obtained from the first through the Atkin–Lehner involution). Assume $k$ is algebraically closed with decidable equality, $q \nmid N$, and let $K$ be an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ that is finite over $\mathbb{Q}$ and such that every $a \in k$ with $a^{q^2} = a$ lies in the image of the coefficient ring $A \cap K$ under `NodeLocalized.redRestrict red K`. Let $w \neq w'$ be two places of the modular function field $\mathbb{F}_k(N) = k(j_q, j_{qN})$ inside Laurent series over $k$, both supersingular in the sense of `ssPlaces q N k`. Then there exist an element $g$ of the base-changed full modular function field of level $Nq$ over $\overline{\mathbb{Q}}$, a proof that its underlying Laurent series lies in `NodeLocalized.jIntegralClosure (N * q) A K` (that is, it lies in the field over $K$ of level $Nq$ and is integral over the $j$-ring of $A$ and $K$), and proofs $h_1$, $h_2$ that $g$ is an integer for $R_1$ and for $R_2$ respectively, such that the residue $R.\mathrm{residue}_1(g)$ has strictly positive order at $w$ and order $0$ at $w'$, while the residue $R.\mathrm{residue}_2(g)$ has strictly positive order at `arithFrobC q k N • w` and order $0$ at `arithFrobC q k N • w'`, where `arithFrobC q k N` is the semilinear automorphism of $\mathbb{F}_k(N)$ induced coefficientwise by the Frobenius of $k$ and acts on places pointwise.
--
--   This is the separation step for supersingular points on the fibre at $q$: it produces a single function of level $Nq$, integral over the $j$-ring of the number field $K$, whose reductions along the two branches vanish at the node attached to $w$ (and at its Frobenius translate) while remaining units at $w'$, the hypothesis on the image of $A \cap K$ supplying enough $\mathbb{F}_{q^2}$-rational supersingular invariants. It feeds the local and Noetherian analysis of the rings of node integers over a prolongation tuple and the determination of the first reduction map up to the arithmetic Frobenius translation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
set_option synthInstance.maxHeartbeats 400000 in

theorem
ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_jIntegralClosure_ord_residues_pos_and_eq_zero_of_ne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    (w w' : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) (hw' : w' ∈ ssPlaces q N k)
    (hne : w ≠ w') :
    ∃ (g : ↥(modularFunctionFieldBar (N * q)))
      (_ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.jIntegralClosure (N * q) A K)
      (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
      0 < w.ord (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) ∧
      0 < (arithFrobC q k N • w).ord (R.residue₂ ⟨g, h₂⟩ : ↥(modularFunctionFieldC k N)) ∧
      w'.ord (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      (arithFrobC q k N • w').ord (R.residue₂ ⟨g, h₂⟩ : ↥(modularFunctionFieldC k N)) = 0 := by sorry
