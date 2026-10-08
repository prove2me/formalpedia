-- Prove2me | Theorems.Thm_OAI_DeligneDrinfeld_NormalizedFamily_bihomogeneous_leading
-- name    : OAI.DeligneDrinfeld.NormalizedFamily.bihomogeneous_leading
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T18:44:16.615851+00:00
-- url     : https://prove2.me/theorems/7ea1c215-2f26-4d14-8689-b8cf67785f7d
-- title:
--   Section 8 with Proposition 5.5 (OpenAI, Deligne–Drinfeld) — leading parts of Ihara words in the chosen generators
-- statement:
--   Everything is over $\mathbb F_2$. Let $g$ be a normalized family (`NormalizedFamily.Data`): values $v_k \in \mathfrak L(x, y)$ for $k \in \mathbb N$ whose Ihara words of odd weight $n$ lie in OpenAI's mod-2 solution space of weight $n$ (`ReducedDimension.solutions n`), a predicate “$k$ is active”, and representatives $\rho_k \in \mathfrak L(A, C, B)$ with $Q(\iota(\rho_k)) = \iota(v_k)$ ($Q$ and $\iota$ as below) such that, for active $k$, every word of $\iota(\rho_k)$ contains $B$ and the first leading part of $\rho_k$ is $(\mathrm{ad}\,x)^{k+1}y$. Let $\Phi_v$ be the Ihara evaluation $\mathfrak L(\sigma_0, \sigma_1, \dots) \to \mathfrak L(x, y)$, the map that sends $\sigma_k$ to $v_k$ and brackets to Ihara brackets (`GenericIhara.evalIhara g.value`), and let $\pi$ send $\sigma_k$ to $(\mathrm{ad}\,x)^{k+1}y$ on associative words (`ImageBound.positiveInput`).
--
--   Let $n, r \in \mathbb N$ and let $p \in \mathfrak L(\sigma_0, \sigma_1, \dots)$ be bihomogeneous: of weight $n$ when $\sigma_k$ weighs $2k + 3$, and of length $r$. Suppose every bracket tree with leaves in $\mathbb N$ of weight $n$ and length $r$ has only active leaves. Then there is $q \in \mathfrak L(A, C, B)$ such that
--
--   1. $Q(\iota(q)) = \iota(\Phi_v(p))$, where $Q$ is the substitution $A \mapsto x^2$, $C \mapsto xy - yx$, $B \mapsto y$ (`QuadraticLeading.under`);
--   2. every word of $\iota(q)$ contains $B$ at least $r$ times;
--   3. the $r$-th leading part of $q$ (its $B$-count-$r$ part after $A \mapsto 0$, $C \mapsto x$, $B \mapsto y$, `ImageBound.leading`) satisfies $\iota(\operatorname{lead}_r(q)) = \pi(\iota(p))$.
--
--   OpenAI, *The Deligne–Drinfeld conjecture* (September 23, 2026), p. 26: “Proposition 5.5 (The leading Ihara bracket). Let $\psi \in F^rL_n$ and $\phi \in F^sL_{n'}$, where $n, n' > 2$ and $r, s \ge 1$. Write $f, g$ for their leading projections at counts $r, s$. Their Ihara bracket, computed in the ambient Lie algebra in $x, y$, belongs to $F^{r+s}$ in the $A, C, B$ presentation, and the projection of its component of count $r + s$ is $[f, g]$.” This is OpenAI's Lean theorem `OAI.DeligneDrinfeld.NormalizedFamily.bihomogeneous_leading` (`lean/OAI/Algebra/Drinfeld`, Apache-2.0), Proposition 5.5 iterated over a bracket word in the generators chosen in §8 (pp. 38–39), so that the “old Hall-word values” there have the expected leading parts. All internal objects are OpenAI's, from the bundle `Def_DeligneDrinfeldInternals`. Published as one of the intermediate statements through which the proof of `OAI.DeligneDrinfeld.main` is checked in pieces.
-- source:
--   OpenAI, The Deligne–Drinfeld conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf, p. 26, Proposition 5.5, as used in Section 8, pp. 38-39; Lean: https://github.com/openai/math/tree/main/lean/OAI/Algebra/Drinfeld (Apache-2.0)

import Mathlib
import Definitions.Def_DeligneDrinfeld
import Definitions.Def_DeligneDrinfeldInternals

namespace OAI.DeligneDrinfeld.NormalizedFamily

theorem bihomogeneous_leading (g : OAI.DeligneDrinfeld.NormalizedFamily.Data)
    {n r : ℕ} {p : FreeLieAlgebra OAI.DeligneDrinfeld.NormalizedFamily.K ℕ}
    (hp : p ∈ OAI.DeligneDrinfeld.LieGrading.biPiece OAI.DeligneDrinfeld.oddWeight (fun x ↦ 1) n r)
    (hactive :
      ∀ (t : OAI.DeligneDrinfeld.UniversalEmbedding.Tree ℕ),
        OAI.DeligneDrinfeld.LieGrading.treeDegree OAI.DeligneDrinfeld.oddWeight t = n →
          OAI.DeligneDrinfeld.LieGrading.treeDegree (fun x ↦ 1) t = r → ∀ k ∈ t.leaves, g.active k) :
    ∃ q,
      OAI.DeligneDrinfeld.QuadraticLeading.under q =
          OAI.DeligneDrinfeld.AssociativeElimination.embed ((OAI.DeligneDrinfeld.GenericIhara.evalIhara g.value) p) ∧
        OAI.DeligneDrinfeld.AssociativeElimination.embed q ∈
            OAI.DeligneDrinfeld.WordGrading.above OAI.DeligneDrinfeld.RowKernel.bCount r ∧
          OAI.DeligneDrinfeld.AssociativeElimination.embed (OAI.DeligneDrinfeld.ImageBound.leading r q) =
            OAI.DeligneDrinfeld.ImageBound.positiveInput (OAI.DeligneDrinfeld.AssociativeElimination.embed p) := by
  sorry

end OAI.DeligneDrinfeld.NormalizedFamily
