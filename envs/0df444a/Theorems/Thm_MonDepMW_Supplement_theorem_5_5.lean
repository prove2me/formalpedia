-- Prove2me | Theorems.Thm_MonDepMW_Supplement_theorem_5_5
-- name    : MonDepMW.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:33:37.235518+00:00
-- url     : https://prove2.me/theorems/f455417c-cbdf-4536-8d2f-3624207529c2
-- title:
--   Theorem 5.5 — $\mathcal T_r$ has subpolynomial growth ratio $\gamma_r(n)$ on $n$-vertex members of a monadically dependent class
-- statement:
--   For every monadically dependent graph class $\mathcal C$ and $r\ge1$ there is a function $\gamma_r:\mathbb N\to\mathbb N$ with $\gamma_r(n)\le\mathrm{subpoly}_{\mathcal C,r}(n)$ such that for every $n$-vertex graph $G\in\mathcal C$, the partition selector $\mathcal T_r$ of $r$-types has growth ratio at most $\gamma_r(n)$ on $G$; that is, for every non-empty $A\subseteq V(G)$,
--
--   $$|\mathcal T_r(G,A)|\le\gamma_r(n)\cdot|A|.$$
--
--   The bound is in terms of the number $n$ of vertices of $G$, not of $|A|$ (the latter is Lemma 5.1). It is the form in which the growth of $r$-types enters the Damping Theorem.
--
--   **Formalization Note** "$\gamma_r(n)\le\mathrm{subpoly}(n)$" is stated as $\gamma_r$ being subpolynomial, which is equivalent since a function below a subpolynomial one is subpolynomial.
--
--   Differences from the source:
--
--   - encoding: γ_r(n) ⩽ subpoly_{C,r}(n) → Subpolynomial γ; reason: a function bounded by a subpolynomial function is subpolynomial, and conversely
--   - encoding: r ∈ N → 1 ≤ r; reason: N is the positive integers (p.11)
--   - encoding: a graph class → MonDepMW.GraphClass (members on each Fin n); reason: every finite graph has a copy on some Fin n and all quantities are isomorphism invariant
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b06082b6e92c2408f95cd60971cd454258095371878ae2f448416bdfeb60b), Theorem 5.5, p.19 (PDF p.21); Definition 5.4 p.19

import Mathlib
import Definitions.Def_MonDepMW_Subpolynomial
import Definitions.Def_MonDepMW_MonadicallyDependent
import Definitions.Def_MonDepMW_PartitionSelector

set_option autoImplicit false

namespace MonDepMW.Supplement

/-- **Theorem 5.5.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded
Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §5.1, p.19 (PDF p.21): "For every monadically dependent
graph class C and r ∈ N, there is a function γr : N → N with γr(n) ⩽ subpoly_{C,r}(n) such that for any n-vertex graph
G ∈ C, Tr has growth ratio at most γr(n) on G."

**Formalization Note.** `r ∈ N` with `N` the positive integers (p.11): `1 ≤ r`. "`γ_r(n) ⩽ subpoly(n)`" is
`Subpolynomial γ` (a function below a subpolynomial one is subpolynomial). "Growth ratio at most `γ`" is
`PartitionSelector.GrowthLE` (Definition 5.4): `|𝒯_r(G, A)| ≤ γ · |A|` for every non-empty `A ⊆ V(G)`. The bound is
evaluated at `n = |V(G)|`, not at `|A|` (that is Lemma 5.1). -/
theorem theorem_5_5 (𝒞 : GraphClass) (h𝒞 : MonadicallyDependent 𝒞) (r : ℕ) (hr : 1 ≤ r) :
    ∃ γ : ℕ → ℕ, Subpolynomial γ ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n → (rTypeSelector r).GrowthLE G (γ n) := by sorry

end MonDepMW.Supplement
