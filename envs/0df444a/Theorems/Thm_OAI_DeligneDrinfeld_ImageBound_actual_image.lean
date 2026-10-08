-- Prove2me | Theorems.Thm_OAI_DeligneDrinfeld_ImageBound_actual_image
-- name    : OAI.DeligneDrinfeld.ImageBound.actual_image
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T18:43:54.909975+00:00
-- url     : https://prove2.me/theorems/07c5d349-9c73-47b4-8cef-1536d019dfe3
-- title:
--   Proposition 5.3 (OpenAI, Deligne–Drinfeld) — the image bound: leading parts come from the free Lie algebra on generators of weights 2k+3
-- statement:
--   Everything is over $\mathbb F_2$. Let $\iota$ denote the embeddings of free Lie algebras over $\mathbb F_2$ into their free associative algebras, let $Q$ be the substitution $A \mapsto x^2$, $C \mapsto xy - yx$, $B \mapsto y$ (`QuadraticLeading.under`), and let $\Phi$ send the generator $e_k$ ($k \ge 0$) of $\mathfrak L(e_0, e_1, \dots)$ to the associative image of $(\mathrm{ad}\,x)^{k+1} y$ (`ImageBound.positiveInput`). For $p \in \mathfrak L(A, C, B)$, its $r$-th leading part (`ImageBound.leading r p`) is obtained from the $B$-count-$r$ part of $p$ by $A \mapsto 0$, $C \mapsto x$, $B \mapsto y$.
--
--   Let $\psi \in \mathfrak L(x, y)$, $p \in \mathfrak L(A, C, B)$, $n > 2$ and $r \in \mathbb N$, and suppose that $\iota(\psi)$ is homogeneous of length $n$, that $Q(\iota(p)) = \iota(\psi)$, that $\psi$ is antisymmetric ($\psi + \psi(y, x) = 0$, `BaseChangeEquations.antisymmetry`), and that every word of $\iota(p)$ contains $B$ at least $r$ times. Then there is $q \in \mathfrak L(e_0, e_1, \dots)$ such that
--
--   $$\Phi(\iota(q)) = \iota(\operatorname{lead}_r(p)),$$
--
--   $\iota(q)$ is homogeneous of weight $n$ when $e_k$ weighs $2k + 3$, and $\iota(q)$ is homogeneous of length $r$.
--
--   OpenAI, *The Deligne–Drinfeld conjecture* (September 23, 2026), p. 24: “Proposition 5.3 (The image bound). Set $g_k = \mathrm{ad}^k_C B$ for $k \ge 1$. These elements freely generate an ordinary free Lie algebra inside $\mathrm{Lie}_{\mathbb F_2}\langle C, B\rangle$. For $n > 2$, the image of the leading projection of $\mathrm{gr}^r_F L_n$ belongs to its weight-$n$, length-$r$ component, where $\mathrm{wt}(g_k) = 2k + 1$ and each $g_k$ has length one.” This is OpenAI's Lean theorem `OAI.DeligneDrinfeld.ImageBound.actual_image` (`lean/OAI/Algebra/Drinfeld`, Apache-2.0), the image bound for the reduction mod 2 of an antisymmetric element, read after $C \mapsto x$, $B \mapsto y$ (OpenAI's generators are indexed from $e_0 \mapsto (\mathrm{ad}\,x) y$, of weight $3$). All objects are OpenAI's, from the bundle `Def_DeligneDrinfeldInternals`. Published as one of the intermediate statements through which the proof of `OAI.DeligneDrinfeld.main` is checked in pieces.
-- source:
--   OpenAI, The Deligne–Drinfeld conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf, p. 24, Proposition 5.3 (the image bound); Lean: https://github.com/openai/math/tree/main/lean/OAI/Algebra/Drinfeld (Apache-2.0)

import Mathlib
import Definitions.Def_DeligneDrinfeldInternals

namespace OAI.DeligneDrinfeld.ImageBound

theorem actual_image {ψ : FreeLieAlgebra OAI.DeligneDrinfeld.ImageBound.K Bool}
    {p : FreeLieAlgebra OAI.DeligneDrinfeld.ImageBound.K OAI.DeligneDrinfeld.RowTwo.Slot} {n r : ℕ} (hn : 2 < n)
    (hψ : OAI.DeligneDrinfeld.AssociativeElimination.embed ψ ∈ OAI.DeligneDrinfeld.WordGrading.homogeneous (fun x ↦ 1) n)
    (hp : OAI.DeligneDrinfeld.QuadraticLeading.under p = OAI.DeligneDrinfeld.AssociativeElimination.embed ψ)
    (hanti : OAI.DeligneDrinfeld.BaseChangeEquations.antisymmetry ψ = 0)
    (hr :
      OAI.DeligneDrinfeld.AssociativeElimination.embed p ∈
        OAI.DeligneDrinfeld.WordGrading.above OAI.DeligneDrinfeld.RowKernel.bCount r) :
    ∃ q,
      OAI.DeligneDrinfeld.ImageBound.positiveInput (OAI.DeligneDrinfeld.AssociativeElimination.embed q) =
          OAI.DeligneDrinfeld.AssociativeElimination.embed (OAI.DeligneDrinfeld.ImageBound.leading r p) ∧
        OAI.DeligneDrinfeld.AssociativeElimination.embed q ∈
            OAI.DeligneDrinfeld.WordGrading.homogeneous OAI.DeligneDrinfeld.ImageBound.oddWeight n ∧
          OAI.DeligneDrinfeld.AssociativeElimination.embed q ∈
            OAI.DeligneDrinfeld.WordGrading.homogeneous (fun x ↦ 1) r := by
  sorry

end OAI.DeligneDrinfeld.ImageBound
