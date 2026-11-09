-- Prove2me | Theorems.Thm_OCTKernel_Main_lemma_3_3
-- name    : OCTKernel.Main.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:17.497945+00:00
-- url     : https://prove2.me/theorems/af8524e1-7888-4ebc-be1f-e7cc3d8fe608
-- title:
--   Lemma 3.3 — Multiplicities in a polynomial space
-- statement:
--   Let $p$ be prime and let $W\subseteq\mathbb F_p[X]$ be an $s$-dimensional space, where $s\ge1$ and all its polynomials have degree at most $d<p$. For each $\alpha\in\mathbb F_p$, let $\nu_W(\alpha)$ be the largest multiplicity at $\alpha$ of a nonzero polynomial in $W$. Then
--
--   $$\sum_{\alpha\in\mathbb F_p}\max\{\nu_W(\alpha)-s+1,0\}\le sd.$$
--
--   The estimate bounds simultaneous large multiplicities across a polynomial space.
--
--   Differences from the source:
--   - encoding: max{ν−s+1,0} over integer differences → natural-number subtraction ν−(s−1); reason: For s≥1 these expressions are identical; subtracting s before adding one would be incorrect.
--   - encoding: a maximum over W minus the zero polynomial → a natural-number supremum of its multiplicities; reason: The nonzero finite-dimensional bounded-degree hypotheses make this set nonempty and bounded, so its supremum is its maximum.
-- source:
--   Tomohiro Koana, Soh Kumabe, A Deterministic Polynomial Kernel for Odd Cycle Transversal, STOC 2027 submission #810 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/810.pdf, SHA-256 043624e22f147583799f7dcc844cebbd4644ecdc53a42543f708cda5c38c6b72, Lemma 3.3, p. 8.

import Definitions.Def_OCTKernel_Main_Polynomials

set_option autoImplicit false

namespace OCTKernel.Main

theorem lemma_3_3 (p s d : ℕ) [Fact p.Prime] (hs : 1 ≤ s) (hd : d < p)
    (W : Submodule (ZMod p) (Polynomial (ZMod p)))
    (hdim : Module.finrank (ZMod p) W = s)
    (hdeg : ∀ f ∈ W, f.degree ≤ (d : WithBot ℕ)) :
    ∑ α : ZMod p, (nu W α - (s - 1)) ≤ s * d := by sorry

end OCTKernel.Main
