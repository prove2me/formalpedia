-- Prove2me | Theorems.Thm_MonDepMW_corollary_5_14
-- name    : MonDepMW.corollary_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:03.023783+00:00
-- url     : https://prove2.me/theorems/c647c6fb-0450-4a3b-ad48-d1649c34e62b
-- title:
--   Corollary 5.14 — orderings of subpolynomial alternation
-- statement:
--   For every monadically dependent graph class $\mathcal C$ there is a function $\alpha$ with $\alpha(n)\leqslant\mathrm{subpoly}_{\mathcal C}(n)$ such that every $n$-vertex $G\in\mathcal C$ admits a vertex ordering of alternation at most $\alpha(n)$. Further, such an ordering can be computed in time $\widehat{\mathcal O}(n^3)$, given $G$ alone.
--
--   The ordering feeds the algorithm of the Damping Theorem.
--
--   **Formalization Note** The factors hidden by $\widehat{\mathcal O}$ may depend on the class. Output: the $n$ vertices in order.
--
--   Differences from the source:
--   - encoding: a graph class → GraphClass, members on each Fin n, no isomorphism closure; reason: every finite graph has a copy on some Fin n, and all quantities are isomorphism invariant
--   - encoding: Ô(n³) → (n+1)³·g(n) with g subpolynomial, g chosen after 𝒞; reason: the paper’s convention (p.11) allows the hidden factors to depend on the fixed class; n+1 only matters at n = 0
--   - encoding: an algorithm on the RAM model with words of length O(log n) (App. C, p.43) → one program of the published word RAM, correct at every word size above b·(⌊log₂(n + inputs + 2)⌋+1), input in fixed cells, output read by a decoder of the output cells and n; reason: the paper names the model only; the layout is fixed once for all items and the decoders never see the input object
--   - encoding: α : N → N with α(n) ⩽ subpoly(n) → α : ℕ → ℕ with Subpolynomial α; reason: a function bounded by a subpolynomial function is itself subpolynomial (squeeze), and conversely; N is the positive integers; the value at 0 is not constrained by the limit and enters only on the empty graph, where every bound holds, or not at all
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), Corollary 5.14, p.22

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_decodeSet
import Definitions.Def_MonDepMW_Subpolynomial
import Definitions.Def_MonDepMW_MonadicallyDependent
import Definitions.Def_MonDepMW_AlternationLE

set_option autoImplicit false

open TrulySubcubicAPSP

namespace MonDepMW

/-- **Corollary 5.14.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.22: "For every monadically dependent graph class C there is a function α : N → N with
α(n) ⩽ subpoly_C(n) such that every n-vertex graph G ∈ C admits a vertex ordering of alternation at most α(n). Further, such a
vertex ordering can be computed in time Ô(n³), given G alone."

**Formalization Note.** The factors hidden by `Ô` may depend on the class, as in the paper's `Ô_q̄` convention (p.11): `g` is
chosen after `𝒞`. Output: the `n` vertices in order. -/
theorem corollary_5_14 (𝒞 : GraphClass) (h𝒞 : MonadicallyDependent 𝒞) :
    ∃ α : ℕ → ℕ, Subpolynomial α ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n → ∃ σ : Fin n ≃ Fin n, AlternationLE G σ (α n)) ∧
      ∃ (P : List Instr) (b : ℕ) (g : ℕ → ℕ), Subpolynomial g ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n → ∀ W : ℕ, b * (Nat.log2 (n + 2) + 1) ≤ W →
          RunsWithin P W ((n + 1) ^ 3 * g n) (graphInput G) fun out =>
            ∃ σ : Fin n ≃ Fin n, (∀ i : Fin n, out i = (((σ i : Fin n) : ℕ) : ℤ)) ∧ AlternationLE G σ (α n) := by sorry

end MonDepMW
