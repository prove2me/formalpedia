-- Prove2me | Theorems.Thm_ModularCurve_exists_irreducible_ramificationIndex_eq_ord_aeval_of_restrict_ne_jLinePlaces
-- name    : ModularCurve.exists_irreducible_ramificationIndex_eq_ord_aeval_of_restrict_ne_jLinePlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/d9c59f6a-f97d-52a7-8ac4-7a0df55b14f2
-- title:
--   Ramification index equals ord_w(p(j)) away from 0,1728,∞
-- statement:
--   Fix $N\ge 1$ and let $j\in\mathbb{Q}((q))$ denote the Laurent series [`ModularCurve.jq`](def/ModularCurve_X0.html#L157); the field $F_N=$ [`ModularCurve.modularFunctionField N`](def/ModularCurve_X0.html#L250) is the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by $j$ and by its $N$-fold $q$-rescaling, viewed as an algebra over the intermediate field $\mathbb{Q}\langle j\rangle$ via [`ModularCurve.jAdjoinAlgebra`](def/ModularCurve_JLinePlaces.html#L19), and it is assumed that $F_N$ is integral over $\mathbb{Q}\langle j\rangle$. Let $w$ be a place of $F_N$ over $\mathbb{Q}$, that is, a proper valuation subring of $F_N$ containing the image of $\mathbb{Q}$ whose ring is a principal ideal ring. Suppose the restriction of $w$ to $\mathbb{Q}\langle j\rangle$ (the preimage valuation subring) is none of the three places `jLinePlace1728`, `jLinePlaceZero`, `jLinePlaceInfty`, obtained by transporting along the isomorphism $\mathbb{Q}(T)\cong\mathbb{Q}\langle j\rangle$, $T\mapsto j$, the places of $\mathbb{Q}(T)$ attached to $T-1728$, to $T$, and to the point at infinity. Then there is a monic irreducible $p\in\mathbb{Q}[X]$ with $p(0)\neq 0$ and $p(1728)\neq 0$ such that $\mathrm{ord}_w(p(j))>0$ and the ramification index of $w$ over $\mathbb{Q}\langle j\rangle$ — the least $n>0$ of the form $\mathrm{ord}_w(f)$ for some nonzero $f$ in the base field — equals $\mathrm{ord}_w(p(j))$, where $\mathrm{ord}_w$ is the normalised additive valuation of $w$ and $p(j)$ denotes the evaluation of $p$ at $j\in F_N$.
--
--   This identifies, for a place of the function field of $X_0(N)$ lying over a closed point of the $j$-line other than $j=0$, $j=1728$ or $j=\infty$, a uniformiser of the base obtained from the monic irreducible polynomial cutting out that closed point, so that the local ramification index is computed as $\mathrm{ord}_w(p(j))$. It is the input used in counting the places where $\mathrm{ord}_w(j)=1$ and where $\mathrm{ord}_w(j-1728)=1$, i.e. in the computations of the elliptic point counts $\nu_3$ and $\nu_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_irreducible_ramificationIndex_eq_ord_aeval_of_restrict_ne_jLinePlaces.lean

import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve

theorem ModularCurve.exists_irreducible_ramificationIndex_eq_ord_aeval_of_restrict_ne_jLinePlaces (N : ℕ) [NeZero N] :
    letI := ModularCurve.jAdjoinAlgebra N
    ∀ [Algebra.IsIntegral ↥ℚ⟮ModularCurve.jq⟯ ↥(ModularCurve.modularFunctionField N)]
      (w : AlgebraicCurve.Place ℚ ↥(ModularCurve.modularFunctionField N)),
      w.restrict ↥ℚ⟮ModularCurve.jq⟯ ≠ ModularCurve.jLinePlace1728 →
      w.restrict ↥ℚ⟮ModularCurve.jq⟯ ≠ ModularCurve.jLinePlaceZero →
      w.restrict ↥ℚ⟮ModularCurve.jq⟯ ≠ ModularCurve.jLinePlaceInfty →
      ∃ p : Polynomial ℚ, Irreducible p ∧ p.Monic ∧ p.eval 0 ≠ 0 ∧ p.eval 1728 ≠ 0 ∧
        0 < w.ord (Polynomial.aeval (⟨ModularCurve.jq, ModularCurve.jq_mem N⟩ : ↥(ModularCurve.modularFunctionField N)) p) ∧
        (w.ramificationIndex ↥ℚ⟮ModularCurve.jq⟯ : ℤ) = w.ord (Polynomial.aeval (⟨ModularCurve.jq, ModularCurve.jq_mem N⟩ : ↥(ModularCurve.modularFunctionField N)) p) := by sorry
