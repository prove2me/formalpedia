-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_integers_nodeResidueFst_ne_zero
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mul_eq_of_mem_integers_nodeResidueFst_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/815d697f-d981-51e3-8b2b-a11449a2247d
-- title:
--   Denominators may be chosen non-vanishing on the first branch
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a nonzero level $N$, a perfect field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ vanishing on $(j, j_q)$) together with the Kronecker congruence $\Phi \bmod q = (X^q - Y)(X - Y^q)$, integrality hypotheses $h\alpha$, $h\beta$ for the two Hecke maps $\overline{\alpha}$, $\overline{\beta}$ at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$, a place specialisation $P$ for these data, and a prolongation tuple $R$ for $P$. Let $K \subseteq \overline{\mathbb{Q}}$ be an intermediate field over $\mathbb{Q}$ and $w$ a place of the function field $\mathrm{modularFunctionFieldC}\ k\ N = k(j \bmod q, j_N \bmod q)$ over $k$. Write $B = R.\mathrm{nodeIntegersOver}\ K\ w$ for the subring of $\mathrm{modularFunctionFieldBar}(Nq)$ consisting of the elements lying in $R.\mathrm{nodeIntegers}\ w$ whose Laurent expansion lies in the field $\mathrm{NodeLocalized.fieldOver}\ (Nq)\ K$, and assume $B$ noetherian. Let $c$ be a system of node coordinates: $x, y \in B$ with $\mathrm{nodeResidue}_1(x) = 0$, $\mathrm{ord}(\mathrm{nodeResidue}_2(x)) = 1$ at the Frobenius translate of $w$, $\mathrm{nodeResidue}_2(y) = 0$ and $w.\mathrm{ord}(\mathrm{nodeResidue}_1(y)) = 1$. Let $\varpi \in A \cap K$ generate the kernel of the reduction $red$ restricted to $A \cap K$, in the sense that an element $d$ of $A \cap K$ reduces to $0$ if and only if $d$ is a multiple of $\varpi$, and let $\varpi_B = R.\mathrm{nodeConst}\ K\ w\ \varpi$ denote its image in $B$ under the constant embedding. Assume: the ideal $(\varpi_B, x, y)$ is maximal and is the unique maximal ideal of $B$; the two branch ideals $(\varpi_B, x)$ and $(\varpi_B, y)$ are prime with $y \notin (\varpi_B, x)$ and $x \notin (\varpi_B, y)$; and $xy = \varpi_B^E u$ for some $E \ge 1$ and some unit $u$ of $B$. Then for any $a, b \in B$ with $b \neq 0$ and any $z$ in the valuation ring $R.R_1.\mathrm{integers}$ of the first regular prolongation satisfying $zb = a$ in $\mathrm{modularFunctionFieldBar}(Nq)$, there exist $a', b' \in B$ with $\mathrm{nodeResidue}_1(b') \neq 0$ and $z b' = a'$.
--
--   This is the ring-theoretic step expressing that the intersection of the first prolongation's valuation ring with the fraction field of the node ring $B$ is the localisation of $B$ at the first branch prime $(\varpi_B, x)$, so that every $B$-fraction integral for the first prolongation can be rewritten with denominator invertible there. It is used in the lemmas computing slope drops and the angular factor at a supersingular node of $X_0(Nq)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_integers_nodeResidueFst_ne_zero.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mul_eq_of_mem_integers_nodeResidueFst_ne_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
      c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (E : ℕ) (hE : 1 ≤ E) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E * u)
    (a b : ↥(R.nodeIntegersOver K w)) (hb : b ≠ 0)
    (z : ↥(modularFunctionFieldBar (N * q))) (hz : z ∈ R.R₁.integers)
    (hzab : z * (b : ↥(modularFunctionFieldBar (N * q))) = a) :
    ∃ a' b' : ↥(R.nodeIntegersOver K w), R.nodeResidue₁ w ⟨b', b'.2.1⟩ ≠ 0 ∧
      z * (b' : ↥(modularFunctionFieldBar (N * q))) = a' := by sorry
