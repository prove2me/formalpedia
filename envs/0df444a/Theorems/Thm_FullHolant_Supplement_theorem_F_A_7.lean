-- Prove2me | Theorems.Thm_FullHolant_Supplement_theorem_F_A_7
-- name    : FullHolant.Supplement.theorem_F_A_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:09:31.180714+00:00
-- url     : https://prove2.me/theorems/a5b1d178-7573-4dc0-9520-2a843512c08f
-- title:
--   Theorem F.A.7 — translation form of the matching family
-- statement:
--   Let $V$ be an eight-element variable set and, for every $e\in\binom V2$, let $P_e$ be a perfect matching of $V\setminus e$. Suppose
--   $$\kappa_r(P_e)=\kappa_e(P_r)\qquad(e\cap r=\varnothing).$$
--   If $P_A\cap P_B=\varnothing$ whenever $A\neq B$ and $A\cap B\neq\varnothing$, then there is a bijection $\iota:V\to\mathbb F_2^3$ such that, after relabelling, for $p\neq q$ and $h=p+q$,
--   $$P_{pq}=\bigl\{\{t,t+h\}:t\in\mathbb F_2^3\setminus\{p,q\}\bigr\},$$
--   where duplicate unordered pairs are suppressed.
--
--   This identifies the matching family of the height-four analysis with the translation structure of $\mathbb F_2^3$ (Lemma F.9.9).
--
--   **Formalization Note** $V$ is any finite type with eight elements; pairs are non-diagonal unordered pairs; $\mathbb F_2^3$ is `Fin 3 → ZMod 2`. "After relabelling" means $P_{\iota^{-1}p,\iota^{-1}q}$ is the $\iota^{-1}$-image of the displayed matching.
--
--   Differences from the source:
--   - encoding: an eight-element variable set V; P_e for e ∈ (V choose 2) → a finite type with `Fintype.card V = 8`; `P : Sym2 V → Finset (Sym2 V)` constrained on non-diagonal pairs; reason: values on diagonal pairs are never used
-- source:
--   Liu–Meng–Wang, A Full Complexity Dichotomy for Complex-Valued Boolean Holant Problems, arXiv:2610.00081 (held version, sha256 d67958c6…), Theorem F.A.7, p.F-78 (PDF p.96); κ_r, p.F-77 (PDF p.95)

import Mathlib
import Definitions.Def_FullHolant_Supplement_MatchingFamily

set_option autoImplicit false

namespace FullHolant.Supplement

/-- **Theorem F.A.7 (Translation form of the matching family).** Let `V` be an eight-element
variable set and, for every `e ∈ (V choose 2)`, let `P_e` be a perfect matching of `V ∖ e`.
Suppose `κ_r(P_e) = κ_e(P_r)` whenever `e ∩ r = ∅`. If `P_A ∩ P_B = ∅` whenever `A ≠ B` and
`A ∩ B ≠ ∅`, then there is a bijection `ι : V → 𝔽₂³` such that, after relabelling, for `p ≠ q` and
`h = p + q`, `P_{pq} = {{t, t + h} : t ∈ 𝔽₂³ ∖ {p, q}}` (duplicate unordered pairs suppressed).
Liu–Meng–Wang, *A Full Complexity Dichotomy for Complex-Valued Boolean Holant Problems*,
arXiv:2610.00081 (held version, sha256 d67958c6…), Theorem F.A.7, p.F-78 (PDF p.96); `κ_r` defined
before (F.61), p.F-77 (PDF p.95).

**Formalization Note.** `V` is any finite type with eight elements; pairs are non-diagonal
`Sym2 V`; `P` is given on all of `Sym2 V`, only its values on pairs are used. `𝔽₂³` is
`Fin 3 → ZMod 2`. "After relabelling" means `P_{ι⁻¹p, ι⁻¹q}` is the `ι⁻¹`-image of the displayed
matching; the `Finset` image suppresses duplicates. -/
theorem theorem_F_A_7 {V : Type*} [Fintype V] [DecidableEq V] (hV : Fintype.card V = 8)
    (P : Sym2 V → Finset (Sym2 V))
    (hP : ∀ e : Sym2 V, ¬ e.IsDiag → IsPerfectMatchingOn (P e) {v | v ∉ e})
    (hκ : ∀ e r : Sym2 V, ¬ e.IsDiag → ¬ r.IsDiag → (∀ v, v ∈ e → v ∉ r) →
      kappa (P e) r = kappa (P r) e)
    (hdisj : ∀ A B : Sym2 V, ¬ A.IsDiag → ¬ B.IsDiag → A ≠ B → (∃ v, v ∈ A ∧ v ∈ B) →
      Disjoint (P A) (P B)) :
    ∃ ι : V ≃ (Fin 3 → ZMod 2), ∀ p q : Fin 3 → ZMod 2, p ≠ q →
      P s(ι.symm p, ι.symm q) =
        ((Finset.univ.filter fun t => t ≠ p ∧ t ≠ q).image
          fun t => s(ι.symm t, ι.symm (t + (p + q)))) := by sorry

end FullHolant.Supplement
