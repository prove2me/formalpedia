-- Prove2me | Theorems.Thm_MonDepMW_lemma_5_3
-- name    : MonDepMW.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:48:54.908046+00:00
-- url     : https://prove2.me/theorems/f56aad64-6091-4055-909b-2eb8194cf74c
-- title:
--   Lemma 5.3 — almost linear growth of $\Gamma$-types
-- statement:
--   Fix a finite set $\Gamma$ of first-order formulas $\varphi(x,y)$, possibly using a fixed finite set of vertex colors, and a monadically dependent graph class $\mathcal C$. There is a function $\gamma_\Gamma$ with $\gamma_\Gamma(n)\leqslant\mathrm{subpoly}_{\mathcal C,\Gamma}(n)$ such that for every $G\in\mathcal C$, every expansion $G^+$ of $G$ by the colors occurring in $\Gamma$, and every non-empty $B\subseteq V(G)$,
--   $$|\mathcal T_\Gamma(G^+,B)|\leqslant|B|\cdot\gamma_\Gamma(|B|).$$
--
--   It lifts Theorem 3.3 to arbitrary formulas, which yields the $r$-type bound.
--
--   **Formalization Note** The colors form `Fin k` for any $k$. Colors occurring in no formula do not affect the partition.
--
--   Differences from the source:
--   - encoding: a graph class → GraphClass, members on each Fin n, no isomorphism closure; reason: every finite graph has a copy on some Fin n, and all quantities are isomorphism invariant
--   - encoding: expansion by the colors occurring in Γ → any c : Fin k → Set (Fin n), with Γ over k colors; reason: colors that occur in no formula of Γ do not affect 𝒯_Γ
--   - encoding: γ_Γ : N → N with γ_Γ(n) ⩽ subpoly(n) → γ_Γ : ℕ → ℕ with Subpolynomial γ_Γ; reason: a function bounded by a subpolynomial function is itself subpolynomial (squeeze), and conversely; N is the positive integers; the value at 0 is not constrained by the limit and enters only on the empty graph, where every bound holds, or not at all
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), Lemma 5.3, p.18

import Mathlib
import Definitions.Def_MonDepMW_Subpolynomial
import Definitions.Def_MonDepMW_MonadicallyDependent
import Definitions.Def_MonDepMW_gammaType
import Definitions.Def_MonDepMW_partsHit

set_option autoImplicit false

namespace MonDepMW

/-- **Lemma 5.3.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.18: "Fix a finite set Γ of first-order formulas φ(x, y), possibly using a fixed finite set of vertex
colors, and a monadically dependent graph class C. There is a function γ_Γ : N → N with γ_Γ(n) ⩽ subpoly_{C,Γ}(n) such that,
for every graph G ∈ C, every expansion G+ of G by the colors occurring in Γ, and every non-empty set B ⊆ V (G), we have
|𝒯Γ(G+, B)| ⩽ |B| · γ_Γ(|B|)."

**Formalization Note.** The fixed colors are `Fin k`, for any `k`; an expansion is any `c : Fin k → Set (Fin n)`. Colors
that occur in no formula of `Γ` do not affect `𝒯_Γ`. -/
theorem lemma_5_3 (k : ℕ) (Γ : Finset ((coloredGraph k).Formula (Fin 2))) (𝒞 : GraphClass)
    (h𝒞 : MonadicallyDependent 𝒞) :
    ∃ γ : ℕ → ℕ, Subpolynomial γ ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n → ∀ (c : Fin k → Set (Fin n)) (B : Finset (Fin n)),
        B.Nonempty → numParts (gammaType Γ G c B) ≤ B.card * γ B.card := by sorry

end MonDepMW
