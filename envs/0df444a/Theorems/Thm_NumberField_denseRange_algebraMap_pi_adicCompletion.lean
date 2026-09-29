-- Prove2me | Theorems.Thm_NumberField_denseRange_algebraMap_pi_adicCompletion
-- name    : NumberField.denseRange_algebraMap_pi_adicCompletion
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:17:22.22426+00:00
-- url     : https://prove2.me/theorems/1bfe4906-6dd0-47cc-84e4-db64b6549549
-- title:
--   Weak approximation at finitely many finite places
-- statement:
--   Let $K$ be a number field and let $S$ be a finite set of pairwise distinct finite places of $K$ (nonzero prime ideals $w$ of $\mathcal O_K$), with $K_w$ the $w$-adic completion. Then the diagonal embedding
--
--   $$
--   K \longrightarrow \prod_{w \in S} K_w, \qquad x \longmapsto (x)_{w \in S},
--   $$
--
--   has dense image (for the product topology).
--
--   Equivalently: given $x_w \in K_w$ for $w \in S$ and $\varepsilon > 0$, there is $x \in K$ with $|x - x_w|_w < \varepsilon$ for all $w \in S$. This is the non-archimedean case of the Artin–Whaples approximation theorem; Mathlib already contains the archimedean analogue `NumberField.InfinitePlace.denseRange_algebraMap_pi`.
--
--   **Formalization Note** $S$ is a `Finset` of `HeightOneSpectrum (𝓞 K)`; the product is indexed by the elements of $S$.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren der math. Wiss. 322, Springer 1999, Chapter II, §3, Approximation Theorem (3.4) (case of finitely many inequivalent non-archimedean valuations of $K$).

import Mathlib

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace NumberField

theorem denseRange_algebraMap_pi_adicCompletion {K : Type*} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (fun x : K => fun w : S =>
      algebraMap K ((w : HeightOneSpectrum (𝓞 K)).adicCompletion K) x) := by sorry

end NumberField
