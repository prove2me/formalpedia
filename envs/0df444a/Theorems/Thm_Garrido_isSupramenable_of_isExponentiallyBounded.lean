-- Prove2me | Theorems.Thm_Garrido_isSupramenable_of_isExponentiallyBounded
-- name    : Garrido.isSupramenable_of_isExponentiallyBounded
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:52:34.341963+00:00
-- url     : https://prove2.me/theorems/90bed23f-42f3-44b3-a26b-bf5874b76c93
-- title:
--   Theorem 3.10(2) — a group of subexponential growth is supramenable
-- statement:
--   If a group $G$ has subexponential growth then $G$ is supramenable: for every
--   nonempty $A \subseteq G$ there is a finitely additive left-invariant
--   $m : \mathcal{P}(G) \to [0,\infty]$ with $m(A) = 1$.
--
--   Subexponential growth is the published `Chou.IsExponentiallyBounded`, which also carries finite
--   generation. Supramenability is strictly stronger than amenability as normalisation is demanded
--   at an arbitrary nonempty set rather than at $G$; note the definition does not require
--   $m(G) = 1$.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 11, Theorem 3.10(2); https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf. Supramenability is attributed in the source to Rosenblatt without a reference. The notion is due to Rosenblatt, who also states this theorem, for every exponentially bounded group, in J. M. Rosenblatt, "Invariant measures and growth conditions", Trans. Amer. Math. Soc. 193 (1974), 33–53, p. 33; https://doi.org/10.1090/S0002-9947-1974-0342955-9

import Mathlib
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Chou_Growth

namespace Garrido

theorem isSupramenable_of_isExponentiallyBounded (G : Type*) [Group G]
    (hG : Chou.IsExponentiallyBounded G) :
    IsSupramenable G := by
  sorry

end Garrido
