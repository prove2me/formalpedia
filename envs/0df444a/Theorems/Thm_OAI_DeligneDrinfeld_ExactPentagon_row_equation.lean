-- Prove2me | Theorems.Thm_OAI_DeligneDrinfeld_ExactPentagon_row_equation
-- name    : OAI.DeligneDrinfeld.ExactPentagon.row_equation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T18:44:28.039191+00:00
-- url     : https://prove2.me/theorems/e41b2775-f4d3-4b84-b5cb-74eae2b83c51
-- title:
--   Proposition 3.2, row form (OpenAI, Deligne–Drinfeld) — the B-count-r part of a mod-2 pentagon solution satisfies the four-row deletion equation
-- statement:
--   Everything is over $\mathbb F_2$. Let $\mathcal A = \mathbb F_2\langle A, C, B\rangle$ be the free associative algebra on the three slots $A, C, B$, with weight $2$ for $A$ and $C$ and $1$ for $B$, and let $\Psi : \mathcal A \to U$ be the mod-2 pentagon map into the enveloping algebra $U$ of the four-strand infinitesimal braid Lie algebra $\mathfrak t_4$ over $\mathbb F_2$: the sum of the five substitutions of the pentagon equation, written in the slots $A \mapsto x^2$, $C \mapsto [x,y]$, $B \mapsto y$ (`PolynomialOrdering.evaluate SourceModel.topFiber SourceModel.topBase ∘ ExactPentagon.full`).
--
--   Let $p, q \in \mathcal A$ and $n, r \in \mathbb N$ with $r < n$. Suppose every word of $p$ has weight $n$, every word of $q$ contains $B$ exactly $r$ times, every word of $p - q$ contains $B$ at least $r + 1$ times (so $q$ is the $B$-count-$r$ part of $p$ and $p$ has no part of lower $B$-count), and $\Psi(p) = 0$. Then for every finite sequence $s$ of slots containing $B$ exactly $r$ times, $q$ satisfies the row equation at $s$ (`RowKernel.Equation q s`):
--
--   $$\tau_1(s, q) + \tau_2(s, q) + \tau_3(s, q) + \tau_4(s, q) = 0 \quad \text{in } \mathbb F_2,$$
--
--   where $\tau_i(s, q)$ is the coefficient of the empty word after the letters of $s$, encoded as $B \mapsto o$, $A \mapsto e$, $C \mapsto p$, are deleted one at a time by the row-$i$ deletion operators of the words of $q$ (each deletion weighted by an explicit $\mathbb F_2$ coefficient of the deleted letter and its two neighbours, the boundary read as $o$ on the left and $w$ on the right).
--
--   OpenAI, *The Deligne–Drinfeld conjecture* (September 23, 2026), p. 11: “Proposition 3.2. Let $\bar\psi \in L_n$, $n > 2$, and suppose its expression $\Psi(A, C, B)$ lies in $F^r$. Let $\chi$ be its component of count $r$, and write $n = 2m + r$, with $m > 0$. In $U(\mathfrak h)$ let $U_{\ell,<r}$ be the span of all products of exactly $\ell$ symbols from $\{a_i, v_{ij}, u_{ij}\}$ that contain fewer than $r$ symbols $u$. Then [the four-term congruence (3.5)] (mod $U_{m+r,<r}$).” This statement is OpenAI's Lean theorem `OAI.DeligneDrinfeld.ExactPentagon.row_equation` (`lean/OAI/Algebra/Drinfeld`, Apache-2.0), which records the leading congruence of §3 in the coordinates that the deletion operators of §4 read off, one equation per row. All objects are OpenAI's, from the bundle `Def_DeligneDrinfeldInternals`. Published as one of the intermediate statements through which the proof of `OAI.DeligneDrinfeld.main` is checked in pieces.
-- source:
--   OpenAI, The Deligne–Drinfeld conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf, p. 11, Proposition 3.2, in the row coordinates of Section 4; Lean: https://github.com/openai/math/tree/main/lean/OAI/Algebra/Drinfeld (Apache-2.0)

import Mathlib
import Definitions.Def_DeligneDrinfeldInternals

namespace OAI.DeligneDrinfeld.ExactPentagon

theorem row_equation  {p q : OAI.DeligneDrinfeld.AssociativeElimination.A OAI.DeligneDrinfeld.RowTwo.K OAI.DeligneDrinfeld.RowTwo.Slot}
    {n r : ℕ} (hp : p ∈ OAI.DeligneDrinfeld.WordGrading.homogeneous OAI.DeligneDrinfeld.ExactPentagon.weight n)
    (hr : r < n) (hq : q ∈ OAI.DeligneDrinfeld.WordGrading.homogeneous OAI.DeligneDrinfeld.RowKernel.bCount r)
    (hhigh : p - q ∈ OAI.DeligneDrinfeld.WordGrading.above OAI.DeligneDrinfeld.RowKernel.bCount (r + 1))
    (hpent :
      (OAI.DeligneDrinfeld.PolynomialOrdering.evaluate OAI.DeligneDrinfeld.SourceModel.topFiber
            OAI.DeligneDrinfeld.SourceModel.topBase)
          (OAI.DeligneDrinfeld.ExactPentagon.full p) =
        0)
    (s : List OAI.DeligneDrinfeld.RowTwo.Slot)
    (hs : OAI.DeligneDrinfeld.WordGrading.degree OAI.DeligneDrinfeld.RowKernel.bCount (FreeMonoid.ofList s) = r) :
    OAI.DeligneDrinfeld.RowKernel.Equation q s := by
  sorry

end OAI.DeligneDrinfeld.ExactPentagon
