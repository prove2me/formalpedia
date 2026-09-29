-- Prove2me | Theorems.Thm_Ideal_exists_span_eq_top_forall_exists_ringHom_localizationAway_idempotent_eq_one
-- name    : Ideal.exists_span_eq_top_forall_exists_ringHom_localizationAway_idempotent_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/c4920731-4dd2-513b-821b-3af10cf49031
-- title:
--   Refining a basic-open cover along orthogonal idempotents
-- statement:
--   Let $S$ be a commutative ring and let $r : \mathrm{Fin}\,m \to S$ be a finite family whose range generates the unit ideal, $\mathrm{span}(\{r_a\}) = \top$. Suppose given, for each index $a$, a natural number $k_a$ and elements $\varepsilon_{a,1},\dots,\varepsilon_{a,k_a}$ of the localisation $S[1/r_a]$ (`Localization.Away (r a)`) which are idempotent ($\varepsilon_{a,i}^2 = \varepsilon_{a,i}$), sum to $1$ over $i$ for each fixed $a$, and are pairwise orthogonal ($\varepsilon_{a,i}\varepsilon_{a,j} = 0$ for $i \neq j$). The conclusion asserts the existence of a natural number $m'$ and a family $t : \mathrm{Fin}\,m' \to S$ whose range again generates the unit ideal, such that for every $b$ there are an index $a$, an index $i \le k_a$, and a ring homomorphism $\rho : S[1/r_a] \to S[1/t_b]$ which is a morphism of $S$-algebras in the sense that $\rho$ composed after $\mathrm{algebraMap}\,S\,S[1/r_a]$ equals $\mathrm{algebraMap}\,S\,S[1/t_b]$, and which satisfies $\rho(\varepsilon_{a,i}) = 1$ and $\rho(\varepsilon_{a,j}) = 0$ for all $j \neq i$.
--
--   This is a purely commutative-algebraic flattening statement for a two-level Zariski covering: a cover of $\operatorname{Spec} S$ by basic open sets together with a decomposition of each piece into clopen parts given by complete orthogonal idempotents can be refined to a single cover by basic open sets on each of which one prescribed idempotent becomes $1$ and the others $0$. It is used in the construction of a common refinement of covers in the theta-level part of the treatment of framed polarised abelian schemes, by [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_cover_isReframe_inter_iso_of_isThetaAdapted_of_iso`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_cover_isReframe_inter_iso_of_isThetaAdapted_of_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_exists_span_eq_top_forall_exists_ringHom_localizationAway_idempotent_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators

theorem Ideal.exists_span_eq_top_forall_exists_ringHom_localizationAway_idempotent_eq_one
    {S : Type} [CommRing S] {m : ℕ} (r : Fin m → S) (hr : Ideal.span (Set.range r) = ⊤)
    (k : Fin m → ℕ) (ε : ∀ a : Fin m, Fin (k a) → Localization.Away (r a))
    (hε₁ : ∀ a i, IsIdempotentElem (ε a i)) (hε₂ : ∀ a, ∑ i, ε a i = 1)
    (hε₃ : ∀ a i j, i ≠ j → ε a i * ε a j = 0) :
    ∃ (m' : ℕ) (t : Fin m' → S), Ideal.span (Set.range t) = ⊤ ∧
      ∀ b : Fin m', ∃ (a : Fin m) (i : Fin (k a)) (ρ : Localization.Away (r a) →+* Localization.Away (t b)),
        ρ.comp (algebraMap S (Localization.Away (r a))) = algebraMap S (Localization.Away (t b)) ∧
        ρ (ε a i) = 1 ∧ ∀ j : Fin (k a), j ≠ i → ρ (ε a j) = 0 := by sorry
