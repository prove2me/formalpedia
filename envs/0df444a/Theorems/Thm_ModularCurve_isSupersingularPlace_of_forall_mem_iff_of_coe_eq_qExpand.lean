-- Prove2me | Theorems.Thm_ModularCurve_isSupersingularPlace_of_forall_mem_iff_of_coe_eq_qExpand
-- name    : ModularCurve.isSupersingularPlace_of_forall_mem_iff_of_coe_eq_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/0a500172-b251-5739-a618-63bd01557b8c
-- title:
--   Supersingularity transfers along the mathsf q ↦ mathsf q^{q^e} substitution
-- statement:
--   Let $q$ be a prime, $N \ge 1$, and $K$ a field of characteristic $q$, and put $E =$ `modularFunctionFieldC K N`, the intermediate field of the Laurent series field $K((\mathsf q))$ generated over $K$ by `jqModC K` (the $q$-expansion of $j$) and `jqNModC K N` $=$ `qExpand K N (jqModC K)`. Let $e \in \mathbb N$ and let $\varphi : E \to E$ be a ring homomorphism which on underlying Laurent series is the substitution $\mathsf q \mapsto \mathsf q^{q^e}$, i.e. the Laurent series of $\varphi(g)$ is `qExpand K (q ^ e)` applied to that of $g$ for every $g \in E$. Let $s, s'$ be places of $E$ over $K$ (valuation subrings of $E$ containing $K$, proper, and principal ideal rings), and assume that for every $g \in E$ one has $g \in \mathcal O_s$ if and only if $\varphi(g) \in \mathcal O_{s'}$, that $s'$ is rational (the map $K \to$ residue field of $s'$ is surjective), and that $s$ is a supersingular place: $s$ is rational, both `jGeomGen K N` and `jNGeomGen K N` lie in $\mathcal O_s$, and the residue value $s.\mathrm{evalAt}$ of `jGeomGen K N` lies in `ssJSet q K`, the set of $j \in K$ such that every elliptic Weierstrass curve over $K$ with $j$-invariant $j$ has no nonzero point killed by $q$. Then $s'$ is likewise a supersingular place.
--
--   This is the statement that the pull-back condition $\mathcal O_s = \varphi^{-1}(\mathcal O_{s'})$ along the $e$-fold Frobenius substitution on $q$-expansions carries supersingular places of the level-$N$ modular function field in characteristic $q$ to supersingular places. It is used in the analysis of the special fibre of the modular curve at $q$, in particular in the uniqueness statements for places lying over a given supersingular place and in the transport of Igusa nodes under level automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isSupersingularPlace_of_forall_mem_iff_of_coe_eq_qExpand.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.isSupersingularPlace_of_forall_mem_iff_of_coe_eq_qExpand
    (q : ℕ) [Fact q.Prime] (N : ℕ) [NeZero N] (K : Type*) [Field K] [DecidableEq K] [CharP K q]
    (e : ℕ) (φ : ↥(modularFunctionFieldC K N) →+* ↥(modularFunctionFieldC K N))
    (hφ : ∀ g : ↥(modularFunctionFieldC K N),
      ((φ g : ↥(modularFunctionFieldC K N)) : LaurentSeries K) = qExpand K (q ^ e) (g : LaurentSeries K))
    (s s' : Place K ↥(modularFunctionFieldC K N))
    (h : ∀ g : ↥(modularFunctionFieldC K N), g ∈ s.toValuationSubring ↔ φ g ∈ s'.toValuationSubring)
    (hs' : s'.IsRational) (hs : IsSupersingularPlace q N K s) :
    IsSupersingularPlace q N K s' := by sorry
