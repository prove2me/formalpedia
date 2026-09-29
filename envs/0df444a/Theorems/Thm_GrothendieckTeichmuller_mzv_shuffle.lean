-- Prove2me | Theorems.Thm_GrothendieckTeichmuller_mzv_shuffle
-- name    : GrothendieckTeichmuller.mzv_shuffle
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T21:52:06.940539+00:00
-- url     : https://prove2.me/theorems/fbc2a00b-3a2d-408a-ad73-456ad42824cc
-- title:
--   Proposition 6.2 — the shuffle relations for multiple zeta values
-- statement:
--   Encode a word $u = n_1\cdots n_k$ of positive integers as the binary word $0^{n_1-1}1\cdots 0^{n_k-1}1$, and let $*$ denote the shuffle product of binary words, the multiset defined by
--
--   $$\alpha w * \alpha' w' = \alpha\,(w * \alpha' w') + \alpha'\,(\alpha w * w').$$
--
--   For a binary word $b$, write $\zeta(b)$ for the multiple zeta value of the word of block lengths obtained by cutting $b$ after each letter $1$.
--
--   Then for all admissible $u$ and $v$ (all letters at least $1$, first letter at least $2$),
--
--   $$\zeta(u)\,\zeta(v) \;=\; \sum_{b\, \in\, \mathrm{bin}(u) \,*\, \mathrm{bin}(v)} \zeta(b),$$
--
--   summed over the multiset with multiplicities. For instance $\zeta(2)\zeta(3) = \zeta(2,3)+3\zeta(3,2)+6\zeta(4,1)$.
--
--   These are the **shuffle relations**, coming from Kontsevich's iterated integral representation of multiple zeta values and the product of two iterated integrals over the same interval. Together with the stuffle relations of Proposition 6.1 they form the double shuffle relations.
-- source:
--   Thomas Willwacher, The Grothendieck-Teichmüller Group, ETH Zürich lecture notes (in progress), 27 February 2014, Section 6.1, p. 53 (definition of multiple zeta values, stuffle product, Proposition 6.1, shuffle product, Proposition 6.2, Euler's identity zeta(2,1) = zeta(3))

import Definitions.Def_GT_multizeta

namespace GrothendieckTeichmuller

theorem mzv_shuffle (u v : List ℕ) (hu : IsAdmissible u) (hv : IsAdmissible v) :
    mzv u * mzv v =
      ((shuffleBin (compToBin u) (compToBin v)).map mzvBin).sum := by sorry

end GrothendieckTeichmuller
