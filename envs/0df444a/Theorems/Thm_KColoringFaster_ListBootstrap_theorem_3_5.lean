-- Prove2me | Theorems.Thm_KColoringFaster_ListBootstrap_theorem_3_5
-- name    : KColoringFaster.ListBootstrap.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:56.346007+00:00
-- url     : https://prove2.me/theorems/64ef25bb-5894-462f-a38a-a365117d66ae
-- title:
--   Theorem 3.5 — (α, Δ)-bounded list coloring (Theorem 1.3 of [Zam21])
-- statement:
--   For every fixed integer $k\ge 1$ and reals $0<\alpha\le 1$, $\Delta>0$, there is a constant $C_{k,\alpha,\Delta}<2$ such that $k$-list-coloring on $n$-vertex $(\alpha,\Delta)$-bounded graphs can be decided in
--   $$O^*\big(C_{k,\alpha,\Delta}^{\,n}\big)$$
--   time, regardless of the size of the color palette, with one-sided error at most $e^{-n}$: no-instances are always rejected, yes-instances are accepted with probability at least $1-e^{-n}$.
--
--   A graph is $(\alpha,\Delta)$-bounded if at least $\alpha n$ of its vertices have degree at most $\Delta$. This is the bounded-degree solver of Theorem 5.1 ("low-degree exit"). It is cited from Zamir, *Breaking the $2^n$ barrier for 5-coloring and 6-coloring*, ICALP 2021, Theorem 1.3; this paper contains no proof of it.
--
--   **Formalization Note** Algorithms and $O^*$ are as in the definition `Algorithms`. The range $\alpha\le 1$ is that of Definition 3.4.
--
--   Differences from the source:
--   - reading: "can be solved" → decided with one-sided error at most $e^{-n}$; reason: §3 (p. 7) allows exponentially small error for all algorithms and says errors can be taken one-sided; $e^{-n}$ is the strongest such bound used in the paper (pp. 8, 25)
--   - encoding: $O^*(\cdot)$ time → one program and polynomials $p,q$ fixed before the input, worst-case cost $\lceil p(\sigma)\,T\rceil$ on the integer RAM with registers of at most $q(\sigma)$ bits; reason: unit cost with polynomially bounded registers equals bit cost up to polynomial factors
--   - encoding: palette $P$ of any size → colors in $\mathbb N$; reason: any finite palette is numbered
--   - generalization: nonempty lists → lists may be empty; reason: instances with an empty list are not colorable and the source's instances are included
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 10, Theorem 3.5 (cited as Theorem 1.3 of Zamir, ICALP 2021); Definition 3.4, p. 9

import Mathlib
import Definitions.Def_KColoringFaster_ListBootstrap_Instances
import Definitions.Def_KColoringFaster_ListBootstrap_Algorithms

open Classical

namespace KColoringFaster.ListBootstrap

/-- Theorem 3.5 ((α, Δ)-bounded List Coloring, Theorem 1.3 of [Zam21]), p. 10. For every fixed
`k ≥ 1`, `0 < α ≤ 1` and `Δ > 0` there is a constant `C < 2` such that k-list-coloring on `n`-vertex
`(α, Δ)`-bounded graphs is decided in `O*(C^n)` time, regardless of the size of the palette, with
one-sided error at most `e^{-n}`. -/
theorem theorem_3_5 (k : ℕ) (hk : 1 ≤ k) (α Δ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hΔ : 0 < Δ) :
    ∃ C : ℝ, C < 2 ∧
      RandDecides encList ListInstance.n (fun I => MaxListLE k I ∧ IsBoundedGraph α Δ I.G)
        ListColorable (fun I => C ^ I.n) (expErr 1) zeroErr := by sorry

end KColoringFaster.ListBootstrap
