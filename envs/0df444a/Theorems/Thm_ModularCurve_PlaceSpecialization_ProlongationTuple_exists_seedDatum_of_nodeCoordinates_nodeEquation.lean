-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_seedDatum_of_nodeCoordinates_nodeEquation
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_seedDatum_of_nodeCoordinates_nodeEquation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/9657dd67-e6ba-5a83-af01-31c859f3b330
-- title:
--   Seed datum from node coordinates with q-normalised node equation
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbf Q}$, a nonzero level $N$, a field $k$ of characteristic $q$ which is algebraically closed, a ring homomorphism $\mathrm{red} : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr` (the bivariate reduction of $\Phi$ modulo $q$ equals $(X^q - X)(X - X^q)$), the integrality hypotheses $h\alpha$, $h\beta$ on the Hecke maps $\overline{\alpha}$, $\overline{\beta}$ at level $N$ and prime $q$, a place specialisation $P$ for these data, a prolongation tuple $R$ over $P$ (carrying in particular two regular prolongations $R_1$, $R_2$ of $A$ on $\overline{F}_{Nq} :=$ `modularFunctionFieldBar (N * q)` with values in the level-$N$ function field over the residue field of $A$), and the hypothesis $q \nmid N$. Let $W$ be a finite set of places of `modularFunctionFieldC k N` over $k$; for each $w \in W$ let $K_w$ be a finite extension of $\mathbf Q$ inside $\overline{\mathbf Q}$, and let $(x_w, y_w)$ be node coordinates at $w$ over $K_w$: elements of the ring $\mathcal O_{K_w,w}$ of those $f \in \overline{F}_{Nq}$ that are $R_1$-integral, $R_2$-integral and lie in every place $V$ of $\overline{F}_{Nq}$ over $\overline{\mathbf Q}$ with $P.\mathrm{reduceFst}(V) = w$, and whose Laurent series lies in the field `NodeLocalized.fieldOver (N * q) K_w`, subject to: the first residue of $x_w$ vanishes, the second residue of $x_w$ has order $1$ at the arithmetic-Frobenius translate of $w$, the second residue of $y_w$ vanishes, and the first residue of $y_w$ has order $1$ at $w$. Let $e$ be a function from places to $\mathbf N$, and for each $w \in W$ let $u_w$ be a unit of $\mathcal O_{K_w,w}$ satisfying the node equation $x_w y_w = c_w(q)^{e(w)} u_w$, where $c_w$ is the constant-embedding homomorphism from $A \cap K_w$ into $\mathcal O_{K_w,w}$ and $q$ is regarded as an element of $A \cap K_w$. Then there exist $y$ and $n$, defined on all places of `modularFunctionFieldC k N`, such that for $w \in W$: $y(w) = y_w$; $n(w) = (\operatorname{lcm}_{w' \in W} e(w'))/e(w)$; $y(w)$ is $R_1$-integral, $R_2$-integral and lies in every place of $\overline{F}_{Nq}$ above $w$; $y(w)$ has nonzero $R_1$-residue; $\operatorname{ord}_V(y(w)) = 0$ for every place $V$ of $\overline{F}_{Nq}$ over $\overline{\mathbf Q}$ with $P.\mathrm{reduceFst}(V) = w$; and for all $w, w' \in W$ the element $y(w)^{n(w)} \, y(w')^{-n(w')}$ is $R_2$-integral with nonzero $R_2$-residue.
--
--   This is the verification that the pair $(y_w, \operatorname{lcm}(e)/e(w))$ built from node coordinates with a $q$-normalised node equation $x_w y_w = q^{e(w)}u_w$ meets the input conditions of the semilocal principality step for the two prolongations, the node equation being the local form of the crossing of the two components of the fibre of $X_0(Nq)$ at a supersingular point. It feeds [`ModularCurve.PlaceSpecialization.exists_isGoodDiv_ord_residueFst_eq_neg_lcm_div_widthChar_of_orderLawFixed`](thm.html#ModularCurve.PlaceSpecialization.exists_isGoodDiv_ord_residueFst_eq_neg_lcm_div_widthChar_of_orderLawFixed), where the resulting functions $y$ and $n$ produce a divisor with prescribed first-residue orders.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_seedDatum_of_nodeCoordinates_nodeEquation.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_seedDatum_of_nodeCoordinates_nodeEquation
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (Ks : ↥W → IntermediateField ℚ (AlgebraicClosure ℚ)) [∀ w : ↥W, FiniteDimensional ℚ (Ks w)]
    (cs : ∀ w : ↥W, R.NodeCoordinates (Ks w) (w : Place k (modularFunctionFieldC k N)))
    (e : Place k (modularFunctionFieldC k N) → ℕ)
    (us : ∀ w : ↥W, ↥(R.nodeIntegersOver (Ks w) (w : Place k (modularFunctionFieldC k N))))
    (hus : ∀ w : ↥W, IsUnit (us w))
    (hxy : ∀ w : ↥W, (cs w).x * (cs w).y =
      R.nodeConst (Ks w) (w : Place k (modularFunctionFieldC k N))
        ((q : ℕ) : ↥(NodeLocalized.coeffSubring A (Ks w))) ^ e (w : Place k (modularFunctionFieldC k N)) * us w) :
    ∃ (y : Place k (modularFunctionFieldC k N) → ↥(modularFunctionFieldBar (N * q)))
      (n : Place k (modularFunctionFieldC k N) → ℕ),
      (∀ (w) (hw : w ∈ W), y w = ((cs ⟨w, hw⟩).y : ↥(modularFunctionFieldBar (N * q)))) ∧
      (∀ w ∈ W, n w = W.lcm e / e w) ∧
      (∀ w ∈ W, y w ∈ R.nodeIntegers w) ∧
      (∀ w ∈ W, ∃ h : y w ∈ R.R₁.integers, R.R₁.residue ⟨y w, h⟩ ≠ 0) ∧
      (∀ w ∈ W, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        P.reduceFst V = w → V.ord (y w) = 0) ∧
      (∀ w ∈ W, ∀ w' ∈ W,
        ∃ h : y w ^ n w * (y w' ^ n w')⁻¹ ∈ R.R₂.integers, R.R₂.residue ⟨y w ^ n w * (y w' ^ n w')⁻¹, h⟩ ≠ 0) := by sorry
