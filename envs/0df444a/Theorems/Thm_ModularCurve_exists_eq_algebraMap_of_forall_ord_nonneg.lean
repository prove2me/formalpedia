-- Prove2me | Theorems.Thm_ModularCurve_exists_eq_algebraMap_of_forall_ord_nonneg
-- name    : ModularCurve.exists_eq_algebraMap_of_forall_ord_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/bd5c35df-5a47-59d8-8d58-5755069d5897
-- title:
--   Everywhere-regular functions on X₀(N)_k are constant
-- statement:
--   Let $q$ be a prime, let $k$ be an algebraically closed field of characteristic $q$, and let $N$ be a nonzero natural number with $q \nmid N$. Write $F =$ `modularFunctionFieldC k N` for the intermediate field of the Laurent series field $k(\!(q)\!)$ obtained by adjoining to $k$ the two elements `jqModC k` $= q^{-1}\cdot(\text{image of the integral power series } \mathtt{jNum} \text{ under } \mathbb{Z}\to k)$ and `jqNModC k N`, the series obtained from the former by the substitution $q \mapsto q^{N}$; thus $F = k(j(q), j(q^{N}))$ inside $k(\!(q)\!)$. Let $h \in F$, and assume that for every place $v$ of $F$ over $k$ — that is, every valuation subring of $F$ which contains $\operatorname{image}(k \to F)$, is not all of $F$, and is a principal ideal ring — one has $0 \le \operatorname{ord}_v(h)$, where $\operatorname{ord}_v$ is the integer-valued order function attached to the height-one prime of that valuation subring. Then $h$ lies in the image of $k$ in $F$: there exists $c \in k$ with $h = \operatorname{algebraMap}_{k \to F}(c)$.
--
--   This is the Liouville-type statement for the complete curve $X_0(N)$ over $k$ in its function-field incarnation: a rational function with no poles at any place is constant. It is used downstream in the analysis of the level-$N$ modular curve over a field of characteristic $q$ prime to $N$, in particular in the study of charts, residues and prolongation data at the places of that curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_eq_algebraMap_of_forall_ord_nonneg.lean

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem ModularCurve.exists_eq_algebraMap_of_forall_ord_nonneg
    {q : ℕ} [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] (N : ℕ) [NeZero N]
    (hqN : ¬ q ∣ N) (h : ↥(modularFunctionFieldC k N))
    (hreg : ∀ v : Place k ↥(modularFunctionFieldC k N), 0 ≤ v.ord h) :
    ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k N) c := by sorry
