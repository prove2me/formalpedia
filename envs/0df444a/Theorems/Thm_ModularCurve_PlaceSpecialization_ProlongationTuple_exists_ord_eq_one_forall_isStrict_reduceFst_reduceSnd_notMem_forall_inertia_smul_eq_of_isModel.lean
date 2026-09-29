-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq_of_isModel
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/90724227-3739-5113-9701-155e225ec076
-- title:
--   Moving lemma on X₀(Nq) with inertia equivariance
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb{Q}}$, $N$ a nonzero level with $q\nmid N$, $k$ an algebraically closed field of characteristic $q$ and $\mathrm{red}\colon A\to k$ a ring homomorphism; let `data` be modular polynomial data for $q$ satisfying the Kronecker congruence (its reduction modulo $q$ is $(C X^{q}-X)(C X-X^{q})$), and assume the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of the level-$N$ into the level-$Nq$ base-changed modular function field over $\overline{\mathbb{Q}}$ are integral. Let $P$ be a place specialisation of these data over $k$ along $\mathrm{red}$, let $W$ be a finite set of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places (rational, affine geometric, with supersingular $j$-value), and let $R$ be a prolongation tuple over $P$ which is a model (the two divisor laws and the two cusp laws), and satisfies the regularity law and the node value law at $W$ and the order law at Frobenius-fixed places. Then for every finite set $T$ of level-$N$ places over $k$ containing no supersingular place, and every place $V_0$ of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb{Q}}$ with $P.\mathrm{reduceFst}\,V_0\in T$ or $P.\mathrm{reduceSnd}\,V_0\in T$, there are a nonzero $f$ in `modularFunctionFieldBar (N * q)` and a divisor $D$ such that: $f$ lies in the valuation rings `R.R₁.integers` and `R.R₂.integers` and both its residues `R.residue₁ f`, `R.residue₂ f` are nonzero; $D$ is the divisor of $f$, i.e. $D(V)=\operatorname{ord}_V(f)$ for all $V$; $D(V_0)=1$; every $V\neq V_0$ in the support of $D$ is strict on the first or second side (respectively $\mathrm{Frob}(\mathrm{reduceFst}\,V)=\mathrm{reduceSnd}\,V$ with $\mathrm{Frob}^2(\mathrm{reduceFst}\,V)\neq\mathrm{reduceFst}\,V$, or $\mathrm{reduceFst}\,V=\mathrm{Frob}(\mathrm{reduceSnd}\,V)$ with $\mathrm{Frob}^2(\mathrm{reduceSnd}\,V)\neq\mathrm{reduceSnd}\,V$, for the geometric Frobenius on level-$N$ places over $k$) and satisfies $\mathrm{reduceFst}\,V\notin T$ and $\mathrm{reduceSnd}\,V\notin T$; and for every $\sigma$ in the inertia subgroup of $A$ inside $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ whose coefficientwise arithmetic action fixes $V_0$, one has $\sigma\cdot f=f$.
--
--   This is the moving lemma used in the analysis of the special fibre of $X_0(Nq)$ at $q$: it produces a function with a prescribed simple zero at $V_0$ whose remaining zeros and poles lie at places that are strict on one of the two sides and reduce outside a prescribed finite set of level-$N$ places, with equivariance under the stabiliser of $V_0$ in the inertia group at $q$. It is the form of the lemma in which the coefficient field $k$ is an arbitrary algebraically closed field of characteristic $q$ receiving $A$, rather than the residue field of $A$, and it is invoked in the construction of inertia-stable degree-zero divisor classes and in the computation of orders at node places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq_of_isModel.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq_of_isModel
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N] (k : Type*) [Field k]
    [CharP k q] (red : A →+* k) (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q) [IsAlgClosed k]
    [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
    (hval : R.NodeValueLaw W) (hO : R.OrderLawFixed) :
        ∀ (T : Finset (Place k ↥(modularFunctionFieldC k N)))
          (hT : ∀ t ∈ T, t ∉ ssPlaces q N k)
          (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
          (hV₀ : P.reduceFst V₀ ∈ T ∨ P.reduceSnd V₀ ∈ T),
          ∃ (f : ↥(modularFunctionFieldBar (N * q)))
            (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
            f ≠ 0 ∧
            (∃ (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
              R.residue₁ ⟨f, h₁⟩ ≠ 0 ∧ R.residue₂ ⟨f, h₂⟩ ≠ 0) ∧
            (∀ V, D V = V.ord f) ∧ D V₀ = 1 ∧
            (∀ V ∈ D.support, V ≠ V₀ → P.IsStrictFst V ∨ P.IsStrictSnd V) ∧
            (∀ V ∈ D.support, V ≠ V₀ → P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T) ∧
            ∀ σ ∈ A.inertiaSubgroupIn ℚ,
              arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V₀ = V₀ →
                arithmeticGalois (modularFunctionFieldFull (N * q)) σ • f = f := by sorry
