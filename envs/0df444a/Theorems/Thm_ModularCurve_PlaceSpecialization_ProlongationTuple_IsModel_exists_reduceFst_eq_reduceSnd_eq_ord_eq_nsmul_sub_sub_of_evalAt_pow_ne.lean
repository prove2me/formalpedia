-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_reduceFst_eq_reduceSnd_eq_ord_eq_nsmul_sub_sub_of_evalAt_pow_ne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_reduceFst_eq_reduceSnd_eq_ord_eq_nsmul_sub_sub_of_evalAt_pow_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/82cfa7d4-958d-59dd-b36f-d1a12b499358
-- title:
--   Multiplication by m on the residue polydisc over a base divisor
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an integer $N \ge 1$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, data $data$ consisting of a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$ together with the Kronecker congruence $hKr$ expressing $\Phi \bmod q = (X^q - Y)(X - Y^q)$, integrality hypotheses $h\alpha, h\beta$ for the two degeneracy embeddings of $\overline{\mathbb Q}$-modular function fields from level $N$ to level $Nq$, and a place specialisation $P$ for these data; assume $q \nmid N$. Let $W$ be a finite set of places of $modularFunctionFieldC\ k\ N$ whose members are exactly the supersingular places (rational, affine for the two geometric coordinates $jGeomGen$, $jNGeomGen$, with $j$-value in $ssJSet$), and let $R$ be a prolongation tuple over $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity and node-value laws at $W$, and the fixed order law. Let $Q_{1,i}$ ($i \in \mathrm{Fin}\ d_1$) be places of $modularFunctionFieldBar(Nq)$ that are strict of the first kind for $P$ (Frobenius carries the first reduction to the second, and the square of Frobenius moves the first reduction) with pairwise distinct first reductions, and $Q_{2,j}$ ($j \in \mathrm{Fin}\ d_2$) strict of the second kind with pairwise distinct second reductions; let $T_1$, $T_2$ be the finite sets of these reductions, with $T_1$ disjoint from $W$. Assume every place of $T_1 \cup T_2$ is affine (both geometric coordinates lie in its valuation subring) and plane-smooth: it has a centre $c = (c_1,c_2) \in k^2$, meaning $jGeomGen - c_1$ and $jNGeomGen - c_2$ both have positive order there, it is the unique place with that centre, and one of these two orders equals $1$; assume moreover coordinate genericity, namely that at each $P.reduceFst(Q_{1,i})$ and each $P.reduceSnd(Q_{2,j})$ the values of both coordinates $x$ satisfy $x^{q^2} \neq x$. Assume the Riemann–Roch hypotheses: every $h$ with non-negative order off $T_1$, order $\ge -1$ on $T_1$ and value $0$ at each place of $W$ vanishes, and every $h$ with non-negative order off $T_2$ and order $\ge -1$ on $T_2$ is a constant; assume $d_1 + d_2 = genusFF$ of $modularFunctionFieldBar(Nq)$ over $\overline{\mathbb Q}$. Let $Q'_{1,i}$, $Q'_{2,j}$ be a second family, strict of the respective kinds and with the same first, resp. second, reductions as $Q_{1,i}$, $Q_{2,j}$; let $Q_s$ be a further strict place of the first kind whose first reduction differs from every $P.reduceFst(Q_{1,i})$; and let $m \in \mathbb N$ with $m \neq 0$ in $k$. Then there are families $Q''_{1,i}$, $Q''_{2,j}$, strict of the first and second kinds respectively, with $P.reduceFst(Q''_{1,i}) = P.reduceFst(Q_{1,i})$ and $P.reduceSnd(Q''_{2,j}) = P.reduceSnd(Q_{2,j})$, and a nonzero $f \in modularFunctionFieldBar(Nq)$ such that for every place $V$ one has $\mathrm{ord}_V(f) = m\,E''(V) - E'(V) - (m-1)E_0(V)$, where $E'' = \sum_i Q''_{1,i} + \sum_j Q''_{2,j}$, $E' = \sum_i Q'_{1,i} + \sum_j Q'_{2,j}$ and $E_0 = \sum_i Q_{1,i} + \sum_j Q_{2,j}$ as divisors.
--
--   In classical terms this is the surjectivity of multiplication by $m$, for $m$ prime to $q$, on the kernel of reduction of the Jacobian of $X_0(Nq)$ at $q$, written in the chart of divisors $E'$ lying in the residue polydisc of a base divisor $E_0$ in general position: the conclusion exhibits $E''$ in the same polydisc with $mE'' \sim E' + (m-1)E_0$. It feeds the divisibility step [`ModularCurve.PlaceSpecialization.IsGluedSpecialization.exists_nsmul_eq_of_isGoodClass_of_apply_eq_zero_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.IsGluedSpecialization.exists_nsmul_eq_of_isGoodClass_of_apply_eq_zero_of_isModel), where good classes annihilated by the glued specialisation are shown to be $m$-divisible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_reduceFst_eq_reduceSnd_eq_ord_eq_nsmul_sub_sub_of_evalAt_pow_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open ModularCurve
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_reduceFst_eq_reduceSnd_eq_ord_eq_nsmul_sub_sub_of_evalAt_pow_ne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k N))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k N v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k N v)
    (hT₁sm : ∀ v ∈ T₁, ∃ c : k × k, IsCentreOf k N c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
      (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hT₂sm : ∀ v ∈ T₂, ∃ c : k × k, IsCentreOf k N c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
      (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hT₁gen : ∀ i, (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N) ∧
      (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k N))
    (hT₂gen : ∀ j, (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N) ∧
      (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k N))
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k N) c)
    (hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i)) (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j))
    (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j))
    (Qs : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQs : P.IsStrictFst Qs)
    (hQs' : ∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i))
    (m : ℕ) (hm : (m : k) ≠ 0) :
    ∃ (Q₁'' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
      (Q₂'' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      (∀ i, P.IsStrictFst (Q₁'' i)) ∧ (∀ j, P.IsStrictSnd (Q₂'' j)) ∧
      (∀ i, P.reduceFst (Q₁'' i) = P.reduceFst (Q₁ i)) ∧
      (∀ j, P.reduceSnd (Q₂'' j) = P.reduceSnd (Q₂ j)) ∧
      ∃ f : ↥(modularFunctionFieldBar (N * q)), f ≠ 0 ∧
        ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          V.ord f =
            (m : ℤ) * ((∑ i, Finsupp.single (Q₁'' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂'' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
            - ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
            - ((m : ℤ) - 1) * ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V) := by sorry
