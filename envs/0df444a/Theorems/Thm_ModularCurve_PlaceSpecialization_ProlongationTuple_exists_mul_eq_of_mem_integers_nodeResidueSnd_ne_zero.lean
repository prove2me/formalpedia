-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_integers_nodeResidueSnd_ne_zero
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mul_eq_of_mem_integers_nodeResidueSnd_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/50d72479-c020-5576-8126-3c2b62c38a0f
-- title:
--   R₂-integral quotients admit denominators with non-zero second residue
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a non-zero level $N$, a perfect field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ with $\Phi(j,j_q)=0$) satisfying the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q)$ modulo $q$, integrality hypotheses $h\alpha$, $h\beta$ for the Hecke maps at level $N$ and prime $q$, a place specialisation $P$ for these data, and a prolongation tuple $R$ over $P$. Let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$, let $w$ be a place of $\mathrm{modularFunctionFieldC}\ k\ N$ over $k$, and write $B = R.\mathrm{nodeIntegersOver}\ K\ w$ for the subring of $\mathrm{modularFunctionFieldBar}\,(Nq)$ consisting of the elements of $R.\mathrm{nodeIntegers}\ w$ whose Laurent expansion lies in $\mathrm{NodeLocalized.fieldOver}\,(Nq)\,K$; $B$ is assumed Noetherian. Let $c$ be a node coordinate pair, i.e. $x, y \in B$ with $\mathrm{nodeResidue}_1(x) = 0$, $\mathrm{ord}$ of $\mathrm{nodeResidue}_2(x)$ equal to $1$ at the place translated by the arithmetic Frobenius, $\mathrm{nodeResidue}_2(y) = 0$ and $w.\mathrm{ord}(\mathrm{nodeResidue}_1(y)) = 1$. Let $\varpi \in A \cap K$ generate the kernel of the reduction on $A \cap K$, in the sense that $d \mapsto \mathrm{redRestrict}\ \mathrm{red}\ K\ d$ vanishes exactly on the multiples of $\varpi$, and write $\varpi_B = R.\mathrm{nodeConst}\ K\ w\ \varpi \in B$ for the corresponding constant. Assume: $(\varpi_B, x, y)$ is maximal and is the only maximal ideal of $B$; the branch ideals $(\varpi_B, x)$ and $(\varpi_B, y)$ are prime with $y \notin (\varpi_B, x)$ and $x \notin (\varpi_B, y)$; and $x y = \varpi_B^{E} u$ for some integer $E \ge 1$ and some unit $u$ of $B$. Finally let $a, b \in B$ with $b \ne 0$ and let $z \in \mathrm{modularFunctionFieldBar}\,(Nq)$ lie in $R.R_2.\mathrm{integers}$ and satisfy $z b = a$. The conclusion is that there exist $a', b' \in B$ with $R.\mathrm{nodeResidue}_2\ w\ b' \ne 0$ and $z b' = a'$.
--
--   This is the prime-avoidance step for the second branch at a supersingular node of $X_0(Nq)$: an element of the second prolongation's valuation ring that is a quotient of node-ring elements can be written with a denominator that does not lie in the branch prime $(\varpi, y) = \ker(\mathrm{nodeResidue}_2|_B)$, the localisation of $B$ at that prime being a discrete valuation ring. It is used in the computations of slope drops and of principal divisors on the special fibre that feed the component-group argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mul_eq_of_mem_integers_nodeResidueSnd_ne_zero.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mul_eq_of_mem_integers_nodeResidueSnd_ne_zero
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
    (z : ↥(modularFunctionFieldBar (N * q))) (hz : z ∈ R.R₂.integers)
    (hzab : z * (b : ↥(modularFunctionFieldBar (N * q))) = a) :
    ∃ a' b' : ↥(R.nodeIntegersOver K w), R.nodeResidue₂ w ⟨b', b'.2.1⟩ ≠ 0 ∧
      z * (b' : ↥(modularFunctionFieldBar (N * q))) = a' := by sorry
