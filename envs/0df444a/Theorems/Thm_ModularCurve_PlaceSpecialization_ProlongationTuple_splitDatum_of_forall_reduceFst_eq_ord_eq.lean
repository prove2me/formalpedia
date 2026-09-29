-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_splitDatum_of_forall_reduceFst_eq_ord_eq
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.splitDatum_of_forall_reduceFst_eq_ord_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/bc79d256-b6b9-5667-b79f-55ba82849554
-- title:
--   Split datum from a local equation at one supersingular node
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a natural number $N\neq 0$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red}:A\to k$, data $\Phi$ of type `ModularPolynomialData q` satisfying the Kronecker congruence `hKr` (its reduction modulo $q$ is $(\,Y^q-X)(Y-X^q)$ in the chosen bivariate normalisation), integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy maps `heckeAlphaBar`, `heckeBetaBar` from level $N$ to level $Nq$, and a place specialisation $P$ for these data. Assume $q\nmid N$. Let $R$ be a prolongation tuple over $P$ which is a model (the two divisor laws and the two cusp laws hold), let $W$ be a finite set of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places `ssPlaces q N k`, and assume $R$ satisfies the regularity law for $W$ and the order law at $\varphi^2$-fixed affine places, where $\varphi=$ `frobOnPlacesGeomLevel k N data hKr`. Let $\pi$ assign to each place a function with $\operatorname{ord}_v(\pi v)=1$ for all $v\in W$, and fix $w\in W$ with $\varphi(\varphi w)=w$. Let $E$ be a divisor on `modularFunctionFieldBar (N * q)` over $\overline{\mathbb Q}$ with $E(V)\ge 0$ for all $V$, each $V$ in the support of $E$ being strict on the first side ($\varphi(\mathrm{red}_1V)=\mathrm{red}_2V$ and $\varphi^2(\mathrm{red}_1V)\neq\mathrm{red}_1V$), or strict on the second side, or satisfying $\mathrm{red}_1V=w$ and strict on neither side, and no support point satisfying `IsCuspidal P` or `IsCuspidal' P`. Let $t$ lie in the integers of both $R.R_1$ and $R.R_2$, with $\operatorname{ord}_V(t)=E(V)$ at every $V$ with $\mathrm{red}_1V=w$ that is strict on neither side. Let $n_1,n_2\in\mathbb N$ and $l_1,l_2\in k^\times$ satisfy $n_1+n_2=(\mathrm{red}_{1*}E)(w)$, let $\pi_w^{-n_1}\cdot R.\mathrm{residue}_1(t)$ take the value $l_1$ at $w$, and let $(\sigma\pi_w)^{-n_2}\cdot R.\mathrm{residue}_2(t)$ take the value $l_2$ at $\sigma w$, where $\sigma=$ `arithFrobC q k N`. Then `R.SplitDatum` holds for $W$, $\pi$, $E$, the divisors $D_1=\mathrm{red}_{1*}(P.\mathrm{fstDiv}\,E)+n_1[w]$ and $D_2=\mathrm{red}_{2*}(P.\mathrm{sndDiv}\,E)+n_2[\sigma w]$, and the multiplier function equal to $l_2l_1^{-1}$ at $w$ and $1$ elsewhere: that is, $\pi$ is a uniformiser along $W$; at every $\varphi^2$-fixed affine place $v$ the values $D_1(v)$ and $D_2(\varphi v)$ lie between the pushforwards of the negative and the positive part of $E$, and $D_1(v)+D_2(\varphi v)=(\mathrm{red}_{1*}E)(v)$; $\deg D_1+\deg D_2=\deg E$; the multiplier is non-zero on $W$; at places not fixed by $\varphi^2$ the divisors $D_1$, $D_2$ agree with the pushforwards of the strict parts of $E$; the infinity-side and zero-side cusp conditions hold; and the concluding condition on functions in the Riemann–Roch space of $E$ integral for both prolongations is satisfied.
--
--   This is the construction, at level $N$ over a prolongation tuple, of a split datum for an effective divisor on $X_0(Nq)_{\overline{\mathbb Q}}$ all of whose non-strict mass lies over a single supersingular node of the special fibre at $q$, the datum being read off from a function $t$ realising $E$ locally there. It feeds the production of good representatives of classes in the Jacobian used in the analysis of the special fibre, being cited by [`ModularCurve.PlaceSpecialization.exists_goodRep_admissible_smul_single_sub_self_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.exists_goodRep_admissible_smul_single_sub_self_of_isModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_splitDatum_of_forall_reduceFst_eq_ord_eq.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization hiding IsCuspidal IsCuspidal'
open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.splitDatum_of_forall_reduceFst_eq_ord_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (hR : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hRL : R.RegularityLaw W) (hO : R.OrderLawFixed)
    (π : Place k (modularFunctionFieldC k N) → modularFunctionFieldC k N) (hπ : ∀ w ∈ W, w.ord (π w) = 1)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hw2 : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hE0 : ∀ V, 0 ≤ E V)
    (hEsupp : ∀ V ∈ E.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨
      (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V))
    (hEc : ∀ V ∈ E.support, ¬ IsCuspidal P V ∧ ¬ IsCuspidal' P V)
    (t : ↥(modularFunctionFieldBar (N * q))) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers)
    (htord : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V) → V.ord t = E V)
    (n₁ n₂ : ℕ) (l₁ l₂ : k) (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (hn : ((n₁ : ℤ) + n₂) = Finsupp.mapDomain P.reduceFst E w)
    (htw₁ : w.HasValue (π w ^ (-(n₁ : ℤ)) * (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC k N))) l₁)
    (htw₂ : (arithFrobC q k N • w).HasValue
      ((arithFrobC q k N • π w) ^ (-(n₂ : ℤ)) * (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k N))) l₂) :
    R.SplitDatum W π E
      (Finsupp.mapDomain P.reduceFst (P.fstDiv E) + Finsupp.single w (n₁ : ℤ))
      (Finsupp.mapDomain P.reduceSnd (P.sndDiv E) + Finsupp.single (arithFrobC q k N • w) (n₂ : ℤ))
      (Function.update (fun _ => (1 : k)) w (l₂ * l₁⁻¹)) := by sorry
