-- Prove2me | Theorems.Thm_ModularCurve_exists_emb_equiv_rootsAt
-- name    : ModularCurve.exists_emb_equiv_rootsAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/82b1c70d-b8c9-54ff-b13e-5bf0adee5677
-- title:
--   Normalised embeddings at j₀ versus roots of Φ_N(j₀+t,Y)
-- statement:
--   Fix a natural number $N$ with $N \neq 0$, a datum `data` consisting of a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$ satisfying $\Phi(j, j_N) = 0$ for the $q$-expansions, and an element $j_0$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Write $H =$ `HahnSeries ℚ (AlgebraicClosure ℚ)` for the Hahn series with rational exponents, and let $\overline{F}_N$ be the intermediate field of $H$ obtained by adjoining to $\overline{\mathbb{Q}}$ the images under coefficientwise base change `coeffEmb` of the elements of `modularFunctionFieldFull N`. Then there is a bijection $e$ between `Emb N j₀`, the set of $\overline{\mathbb{Q}}$-algebra homomorphisms $\psi : \overline{F}_N \to H$ with $\psi(\bar{\jmath}) = j_0 + t$, where $\bar{\jmath}$ is the base change of the Laurent series `jq` and $j_0 + t$ denotes `HahnSeries.C j₀ + HahnSeries.single 1 1`, and `RootsAt data (jNear j₀)`, the set of $y \in H$ that are roots of the polynomial obtained from $\Phi$ by substituting $j_0 + t$ for $X$; moreover $e$ satisfies $e(\psi) = \psi(\bar{\jmath}_N)$ for all $\psi$, where $\bar{\jmath}_N$ is the base change of `qExpand ℚ N jq`, the series `jq` with $q$ replaced by $q^N$.
--
--   This is the dictionary between normalised Puiseux-type embeddings of the function field of $X_0(N)$ over $\overline{\mathbb{Q}}$ sending $j$ to $j_0 + t$ and roots of the specialised modular polynomial $\Phi_N(j_0 + t, Y)$, the bijection being evaluation at $j(q^N)$. It feeds the construction of elliptic models with a distinguished cyclic subgroup, being used by [`ModularCurve.exists_elliptic_cycSub_orbitMap_of_props`](thm.html#ModularCurve.exists_elliptic_cycSub_orbitMap_of_props) and [`ModularCurve.exists_elliptic_cycSub_orbitMap_prime_of_ne_two`](thm.html#ModularCurve.exists_elliptic_cycSub_orbitMap_prime_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_emb_equiv_rootsAt.lean

import Mathlib
import Definitions.Def_ModularCurve_EMD
import Definitions.Def_ModularCurve_TatePoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_emb_equiv_rootsAt (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (j₀ : AlgebraicClosure ℚ) :
    ∃ e : ModularCurve.Emb N j₀ ≃ ModularCurve.TatePoint.RootsAt data (ModularCurve.TatePoint.jNear j₀),
      ∀ ψ : ModularCurve.Emb N j₀, (e ψ).1 = ψ.1 ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ N ModularCurve.jq),
        ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.jqd_mem_full N (dvd_refl N))⟩ := by sorry
