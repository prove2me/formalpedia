-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq
-- name    : ModularCurve.PlaceSpecialization.exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/0698d83d-7095-588b-a5d2-41780c92d5bb
-- title:
--   Inertia-fixed strict families of places at level Nq
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive integer $N$, and an algebraically closed field $k$ of characteristic $q$ together with a ring homomorphism $\mathrm{red} : A \to k$. Fix further `data : ModularPolynomialData q`, i.e. a monic $\Phi \in (\mathbb{Z}[X])[Y]$ of degree $\psi(q)$ annihilating the $q$-th modular expansion, a hypothesis `hKr` that the reduction of $\Phi$ modulo $q$ equals $(X^q - Y)(X - Y^q)$ in the bivariate sense of `KroneckerCongruence`, and hypotheses `hα`, `hβ` that the ring homomorphisms underlying `heckeAlphaBar` and `heckeBetaBar` from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$ are integral. Let $P$ be a `PlaceSpecialization` for these data, so in particular $P$ carries a map $P.\mathrm{sp}$ from places of `modularFunctionFieldBar N` to places of `modularFunctionFieldC k N` subject to the structure's compatibility axioms, and assume $q \nmid N$. Then for every finite set $B$ of places of `modularFunctionFieldC k N` and all $m_1, m_2 \in \mathbb{N}$ there exist families $Q_1 : \mathrm{Fin}\,m_1$ and $Q_2 : \mathrm{Fin}\,m_2$ of places of `modularFunctionFieldBar (N * q)` such that each $Q_1(i)$ satisfies `P.IsStrictFst` and each $Q_2(j)$ satisfies `P.IsStrictSnd`, where, writing $r_1(W) = P.\mathrm{sp}(W|_{\text{heckeAlphaBar}})$ and $r_2(W) = P.\mathrm{sp}(W|_{\text{heckeBetaBar}})$ for the two reductions, `IsStrictFst` says that `frobOnPlacesGeomLevel k N data hKr` sends $r_1(W)$ to $r_2(W)$ and that its square does not fix $r_1(W)$, while `IsStrictSnd` says that it sends $r_2(W)$ to $r_1(W)$ and that its square does not fix $r_2(W)$; moreover $i \mapsto r_1(Q_1(i))$ and $j \mapsto r_2(Q_2(j))$ are injective, all these reductions lie outside $B$, and every $Q_1(i)$ and every $Q_2(j)$ is fixed by $\mathrm{arithmeticGalois}(\text{modularFunctionFieldFull}(Nq))(\sigma)$ for all $\sigma$ in `A.inertiaSubgroupIn ℚ`, the image in $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of the inertia subgroup of $A$ inside its decomposition subgroup.
--
--   This supplies, in arbitrary prescribed numbers and avoiding any prescribed finite set of places of the level-$N$ fibre in characteristic $q$, auxiliary places of the level-$Nq$ modular function field over $\overline{\mathbb{Q}}$ that are strict of each of the two kinds and are in addition fixed by the inertia group of $A$; it strengthens the corresponding statement without the inertia clauses. It is used in the construction of Deligne–Rapoport model packages for $X_0(Nq)$ and of their resolved and level versions, the geometric input to Ribet's level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq.lean

import Definitions.Def_ModularCurve_GlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (B : Finset (Place k (modularFunctionFieldC k N))) (m₁ m₂ : ℕ) :
    ∃ (Q₁ : Fin m₁ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      (Q₂ : Fin m₂ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
      (∀ i, P.IsStrictFst (Q₁ i)) ∧ (∀ j, P.IsStrictSnd (Q₂ j)) ∧
      (Function.Injective fun i => P.reduceFst (Q₁ i)) ∧
      (Function.Injective fun j => P.reduceSnd (Q₂ j)) ∧
      (∀ i, P.reduceFst (Q₁ i) ∉ B) ∧ (∀ j, P.reduceSnd (Q₂ j) ∉ B) ∧
      (∀ i, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q₁ i = Q₁ i) ∧
      (∀ j, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • Q₂ j = Q₂ j) := by sorry
