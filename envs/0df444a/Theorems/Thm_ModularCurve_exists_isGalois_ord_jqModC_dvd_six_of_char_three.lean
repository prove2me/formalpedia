-- Prove2me | Theorems.Thm_ModularCurve_exists_isGalois_ord_jqModC_dvd_six_of_char_three
-- name    : ModularCurve.exists_isGalois_ord_jqModC_dvd_six_of_char_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/a43c8adf-d806-51ba-943e-501f23e10afe
-- title:
--   Galois model over K(j) with ramification dividing 6, characteristic 3
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $3$ and let $N\ge 1$ be an integer which is nonzero in $K$ (equivalently, $3\nmid N$). Write $\mathrm{jq} = q^{-1}\cdot\overline{(E_4^3\,\eta^{-24})} \in K((q))$ for the Laurent series `jqModC K`, the reduction to $K$ of the integral $q$-expansion of $j$, and let $F$ be the intermediate field `modularFunctionFieldFullC K N` of $K((q))$ obtained by adjoining to $K$ all the series $\mathrm{jq}(q^d)$ for nonzero divisors $d\mid N$; thus $\mathrm{jq}$ itself (the case $d=1$) is an element of $F$. The assertion is that there exist a field $M$ in the same universe as $K$, a $K$-algebra structure on $M$, and a $K$-algebra homomorphism $\iota : F \to M$, such that, setting $t = \iota(\mathrm{jq})$ and letting $K(t)\subseteq M$ be the intermediate field generated over $K$ by $t$: (i) $M$ is finite-dimensional over $K(t)$; (ii) $M$ is Galois over $K(t)$; and (iii) for every place $P$ of $M$ over $K$ — a proper valuation subring of $M$ containing $K$ whose ring is a principal ideal ring — with $\mathrm{ord}_P(t) > 0$, one has $\mathrm{ord}_P(t) \mid 6$, where $\mathrm{ord}_P$ is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation.
--
--   This provides a finite Galois cover $M/K(j)$ in characteristic $3$ through which the full level-$N$ modular function field factors, with the ramification index at every place above $j=0$ dividing $6$ — the characteristic-$3$ phenomenon that $j=0=1728$ carries a curve with extra automorphisms. It feeds the local analysis at $j=0$ used in [`ModularCurve.seven_le_ordDiff_D_jqModC_of_ord_eq_six`](thm.html#ModularCurve.seven_le_ordDiff_D_jqModC_of_ord_eq_six).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isGalois_ord_jqModC_dvd_six_of_char_three.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

universe u in

theorem ModularCurve.exists_isGalois_ord_jqModC_dvd_six_of_char_three
    (K : Type u) [Field K] [IsAlgClosed K] [CharP K 3] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    ∃ (M : Type u) (_ : Field M) (_ : Algebra K M) (ι : modularFunctionFieldFullC K N →ₐ[K] M),
      FiniteDimensional
          (IntermediateField.adjoin K ({ι ⟨jqModC K, jqModC_mem_full K N⟩} : Set M)) M ∧
        IsGalois
          (IntermediateField.adjoin K ({ι ⟨jqModC K, jqModC_mem_full K N⟩} : Set M)) M ∧
        ∀ P : Place K M, 0 < P.ord (ι ⟨jqModC K, jqModC_mem_full K N⟩) →
          P.ord (ι ⟨jqModC K, jqModC_mem_full K N⟩) ∣ 6 := by sorry
